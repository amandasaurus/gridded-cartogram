import fiona
import shapely.geometry, shapely.geos, shapely.ops
import copy
import math
from collections import defaultdict, deque
import itertools
import argparse
import csv
import collections

class GriddfyError(Exception):pass
class InvalidGeometryError(GriddfyError): pass


def mean(input_list):
    """Artimetic mean of a iterator of numbers. Returns 0 if empty"""
    num_seen = 0
    total = 0
    for num in input_list:
        total += num
        num_seen += 1

    if num_seen == 0:
        return 0
    else:
        return total / num_seen


def frange(start, end, step):
    """Floating point range."""
    curr = start
    while curr < end:
        yield curr
        curr += step


def open_input_source(filename):
    results = []
    with fiona.open(filename) as source:
        for record in source:
            shape = shapely.geometry.shape(record['geometry'])
            results.append({'shape': shape, 'id':record['id'], 'properties':record['properties'], 'geometry':record['geometry']})
        meta = source.meta

    return results, meta


def convert_objects_to_geojson_geometry(objects):
    results = []
    for obj in objects:
        assert 'shape' in obj
        new_obj = {}
        for key in obj:
            if key not in ['shape', 'geometry']:
                new_obj[key] = copy.deepcopy(obj[key])
            new_obj['geometry'] = shapely.geometry.mapping(obj['shape'])
        results.append(new_obj)

    return results


def write_shapefile(filename, objects, metadata):
    with fiona.open(filename, 'w', driver=metadata['driver'], crs=metadata['crs'], schema=metadata['schema']) as output:
        for obj in objects:
            output.write(obj)


def match_up_property(input_objects, property_to_grid_on):
    for obj in input_objects:
        obj['property_to_grid_on'] = obj['properties'][property_to_grid_on]
    return input_objects


def get_bbox(input_objects):
    """"Aggregate bbox of a list of objects."""
    assert len(input_objects) > 0
    first_bounds = input_objects[0]['shape'].bounds
    minx, miny, maxx, maxy = first_bounds
    for obj in input_objects:
        bounds = obj['shape'].bounds
        minx = min(minx, bounds[0])
        miny = min(miny, bounds[1])
        maxx = max(maxx, bounds[2])
        maxy = max(maxy, bounds[3])

    return (minx, miny, maxx, maxy)


def cover_with_sqares(bounds, density):
    """Given a bounding box (minx, miny, maxx, maxy) and a witth, return a list of shapely geometry objects competly covering this area. May go over the ends."""
    width = square_width_for_area(density)
    minx, miny, maxx, maxy = bounds
    assert minx < maxx
    assert miny < maxy

    x, y = minx, miny
    results = []
    for x in frange(minx, maxx, width):
        for y in frange(miny, maxy, width):
            results.append(shapely.geometry.box(x, y, x+width, y+width))

    return results


def square_width_for_area(desired_area):
    """Given an area, what's the length of the side of the square we need."""
    width = math.sqrt(desired_area)
    return width


def hexagon_radius_for_area(desired_area):
    return math.sqrt( (2 * desired_area) / (3 * math.sqrt(3)) )


def hexagon_points(centre, radius):
    cx, cy = centre
    r_root_3_half = (radius * math.sqrt(3)) / 2
    r_half = radius / 2
    # Starting at due left of centre, and working clock wise
    return [
        (cx - radius, cy),  # a
        (cx - r_half, cy + r_root_3_half),  # b
        (cx + r_half, cy + r_root_3_half),  # c
        (cx + radius, cy),  # d
        (cx + r_half, cy - r_root_3_half),  # e
        (cx - r_half, cy - r_root_3_half),  # f
    ]


def cover_with_hexagons(bounds, density):
    """Given a bounding box (minx, miny, maxx, maxy) and a witth, return a list of shapely geometry objects competly covering this area. May go over the ends."""
    radius = hexagon_radius_for_area(density)

    minx, miny, maxx, maxy = bounds
    assert minx < maxx
    assert miny < maxy

    x, y = minx, miny
    results = []
    y_row = 0
    for y in frange(miny, maxy, (radius*math.sqrt(3))/2):
        x_offset = 1.5 * radius if ( y_row % 2 == 0 ) else 0

        for x in frange(minx, maxx, radius*3):
            x += x_offset
            results.append(shapely.geometry.Polygon(hexagon_points((x, y), radius)))

        y_row += 1

    return results


def square_width_for_area(desired_area):
    """Given an area, what's the length of the side of the square we need."""
    width = math.sqrt(desired_area)
    return width


def remove_non_overlapping(desired_num, cells, input_shapes):
    assert desired_num <= len(cells)
    if len(cells) == desired_num:
        return cells

    cells_that_overlap = [cell for cell in cells if any(cell.intersects(obj['shape']) for obj in input_shapes)]
    if len(cells_that_overlap) < desired_num:
        # we need to pull in so other ones, adding cells that are closer to
        # existing polygons
        non_overlapping_cells = [cell for cell in cells if cell not in cells_that_overlap]
        non_overlapping_cells.sort(key=lambda cell: min(cell.distance(obj['shape']) for obj in input_shapes))
        extra_needed = desired_num - len(cells_that_overlap)
        cells_that_overlap.extend(non_overlapping_cells[:extra_needed])

    return cells_that_overlap


def find_neighbours(cells):
    """Given a list of shapely geometries, return a dict of what index'ed shape touches other indexes."""
    results = {}
    # FIXME could probably do this more effecient
    for cellid, cell in enumerate(cells):
        # Don't include diagonal touchings
        neighbours = {cid for (cid, c) in enumerate(cells) if cid != cellid and cell.touches(c) and cell.intersection(c).geom_type != 'Point'}
        results[cellid] = neighbours

    return results

def confirm_all_input_geoms_valid(objects):
    invalid_shapes = [o for o in objects if not o['shape'].is_valid]
    if len(invalid_shapes) == 0:
        return
    else:
        print("There are {} objects with invalid shapes".format(len(invalid_shapes)))
        for o in invalid_shapes:
            print(" Object id {} is invalid".format(o['id']))
        raise InvalidGeometryError


def possible_cells_for_polygon(cells_to_choose_from, num_needed, cell_neighbours):
    """
    Given cells_to_choose_from which is a cells that cover a polygon, and we
    need num_needed, generate the possible combinations of cells that will all
    touch each other
    """
    assert len(cells_to_choose_from) >= num_needed

    has_found_a_connected_permutation = False

    # TODO this could be speed up by not taking all combinations, but by
    # filtering them as they are generated, i.e. write own permutations
    # generator, like the prune/product
    for permutation in itertools.combinations(cells_to_choose_from, int(num_needed)):
        assert len(set(permutation)) == len(permutation), "Duplicates in permutation?"
        permutation = set(permutation)

        assert len(permutation) > 0

        # This permutation is only OK if they aren't disjoint.
        unsure_cells = permutation.copy()
        ok_cells = {unsure_cells.pop()}
        while len(unsure_cells) > 0:
            cells_that_neighbour_ok_cells = {cellid for cellid in unsure_cells if any(cellid in cell_neighbours[okcellid] for okcellid in ok_cells)}
            if len(cells_that_neighbour_ok_cells) == 0:
                # Bad permutation, there are no more neighbouring cells
                break
            else:
                # The cells in cells_that_neighbour_ok_cells are now OK
                # cells. So add them to ok_cells and remove them from
                # unsure_cells
                ok_cells.update(cells_that_neighbour_ok_cells)
                unsure_cells.difference_update(cells_that_neighbour_ok_cells)
        else:
            # Loop terminated without break-ing out, so this is a good
            # permutation
            yield permutation
            has_found_a_connected_permutation = True

    if has_found_a_connected_permutation:
        return

    # If there is no connected permutation, allow permutations which are split
    # into 2 groups
    for permutation in itertools.combinations(cells_to_choose_from, int(num_needed)):
        permutation = set(permutation)

        # This permutation is only OK if they aren't disjoint.
        unsure_cells = permutation.copy()
        ok_cells_group1 = {unsure_cells.pop()}
        ok_cells_group2 = set()
        while len(unsure_cells) > 0:
            cells_that_neighbour_ok_cells1 = {cellid for cellid in unsure_cells if any(cellid in cell_neighbours[okcellid] for okcellid in ok_cells_group1)}
            if len(cells_that_neighbour_ok_cells1) == 0:
                # Bad permutation, there are no more neighbouring cells in
                # group1, try group2:
                if len(ok_cells_group2) == 0:
                    # start our other group
                    cells_that_dont_neighbour_ok_cells1 = {cellid for cellid in unsure_cells if not any(cellid in cell_neighbours[okcellid] for okcellid in ok_cells_group1)}
                    ok_cells_group2.add(cells_that_dont_neighbour_ok_cells1.pop())
                else:
                    cells_that_neighbour_ok_cells2 = {cellid for cellid in unsure_cells if any(cellid in cell_neighbours[okcellid] for okcellid in ok_cells_group2)}
                    if len(cells_that_neighbour_ok_cells2) == 0:
                        # nothing here either
                        break
                    else:
                        ok_cells_group2.update(cells_that_neighbour_ok_cells2)
                        unsure_cells.difference_update(cells_that_neighbour_ok_cells2)
            else:
                ok_cells_group1.update(cells_that_neighbour_ok_cells1)
                unsure_cells.difference_update(cells_that_neighbour_ok_cells1)
        else:
            # good permutation
            yield permutation


def product_but_prune_dupe_cells(input_shapes, cell_neighbours, cells):
    curr_pos = []
    stack_to_visit = deque()
    stack_to_visit.extend([i] for i in range(len(input_shapes[0]['cell_permutations'])))
    assert len(stack_to_visit) > 0, "WTF, no options to search?"

    while len(stack_to_visit) > 0:
        curr_pos = stack_to_visit.popleft()
        curr_results = [input_shapes[idx]['cell_permutations'][x] for idx, x in enumerate(curr_pos)]
        if len(curr_pos) == len(input_shapes):
            # we've got a leaf node, so yield that result
            print("LEAF NODE")
            print("{0:3d} {1:3d} {2}".format(len(curr_pos), len(input_shapes), curr_pos))
            yield [{'id': obj['id'], 'num': obj['num'], 'cells_results':result} for (obj, result) in zip(input_shapes, curr_results)]
        else:
            depth = len(curr_pos)
            num_child_nodes = len(input_shapes[depth]['cell_permutations'])
            assert num_child_nodes > 0
            seen_cell_ids = set.union(*[set(x) for x in curr_results])

            # These are the cells that border the cells we already have
            # allocated
            possible_neighbours = set.union(*[set(cell_neighbours[x]) for x in seen_cell_ids])

            for new_id in range(num_child_nodes):
                possible_new_cells = input_shapes[depth]['cell_permutations_as_set'][new_id]
                # but exclude/"prune" ones that we already have seen
                if not possible_new_cells.isdisjoint(seen_cell_ids):
                    # has dupes! So don't add it
                    # using this permutation would make one cell covering more
                    # than 1 polygon, which is impossible
                    continue
                elif not any(x in possible_neighbours for x in possible_new_cells):
                    # None of the cells touch any of the existing cells we
                    # have. skip this permutation
                    continue
                elif has_single_cell_hole(curr_results + [input_shapes[depth]['cell_permutations'][new_id]], cell_neighbours):
                    #print "Found simple hole"
                    continue
                elif has_holes(curr_results + [input_shapes[depth]['cell_permutations'][new_id]], cell_neighbours):
                    # we've created a hole, skip it
                    #print "Found complex hole"
                    continue
                else:
                    # No, dupes, it's good to visit
                    stack_to_visit.appendleft(curr_pos + [new_id])

    print("Came to end!!!")


def has_single_cell_hole(full_cells, cell_neighbours):
    full_cells = set.union(*[set(x) for x in full_cells])
    all_cells = set(cell_neighbours.keys())
    empty_cells = all_cells - full_cells

    for empty_cell in empty_cells:
        if all(neighbour in full_cells for neighbour in cell_neighbours[empty_cell]):
            # This cell is empty, and all the other cells are full. Ergo this
            # is a hole
            return True

    return False


def has_holes(full_cells, cell_neighbours):
    full_cell_ids = set.union(*[set(x) for x in full_cells])
    all_cell_ids = set(cell_neighbours.keys())
    max_possible_neighbours = max(len(neighbour) for neighbour in cell_neighbours.values())
    empty_cell_ids = all_cell_ids - full_cell_ids

    if len(empty_cell_ids) == 0:
        return False

    edge_cell_ids = {cellid for cellid in all_cell_ids if len(cell_neighbours[cellid]) < max_possible_neighbours}
    assert len(edge_cell_ids) > 0

    # Now grow the edge cells outwards.
    # We add cells that neighbour any cell in edge_cell_ids that are empty
    while True:
        border_edges = {cellid for cellid in empty_cell_ids if cellid not in edge_cell_ids and any(cellid in cell_neighbours[existing_edge_cell] for existing_edge_cell in edge_cell_ids)}
        if len(border_edges) == 0:
            # we've expanded as far as we can go
            break
        else:
            # grow the edge_cell_ids set
            edge_cell_ids.update(border_edges)

    # Do we have cellids that are empty and *not* in border_edges? then they
    # must be inner holes
    inner_holes = empty_cell_ids - edge_cell_ids
    if len(inner_holes) > 0:
        return True
    else:
        return False


def intersection_percent(a, b):
    """For 2 shapely shapes, return what percentage of a is covered by b. If b is invalid, 0 is returned."""
    try:
        if a.intersects(b):
            intersection = a.intersection(b)
            return intersection.area / a.area
        else:
            return 0
    except shapely.geos.TopologicalError:
        # likely that b is invalid geometry
        return 0


def sort_input_shapes_by_touching(polygon_cells):
    result = [polygon_cells[0]]
    remaining = polygon_cells[1:]

    def _num_shared_cells(obj, result):
        """Given an obj, and list of obj's (result), return the number of shared cells obj has with all the cells in result."""
        cells = set(obj['cells'])
        all_other_cells = set.union(*[set(x['cells']) for x in result])
        return len(all_other_cells & cells)

    while len(remaining) > 0:
        # sort by closness
        # maybe only taking last 5 will make it "locally aware".
        remaining.sort(key=lambda x, result=result[-5:]: _num_shared_cells(x, result), reverse=True)
        result.append(remaining.pop(0))

    return result


def all_possibilities_for_cell_match_up(cells, input_shapes):
    cell_neighbours = find_neighbours(cells)
    assert any(len(neighbours) > 0 for neighbours in cell_neighbours.values()), "No cell touches any other"

    # {'cell-index': [input_shapes['id'], ... ], ... }
    cells_cover_what_polygons = defaultdict(list)
    polygon_cells = []
    polygon_cells_extreme = []

    for obj in input_shapes:
        num = obj['property_to_grid_on']
        cells_covering = [(idx, cell, intersection_percent(cell, obj['shape'])) for (idx, cell) in enumerate(cells) if cell.intersects(obj['shape'])]
        polygon_cells.append({'id': obj['id'], 'num': num, 'cells': [x[0] for x in cells_covering]})
        for cell_id, cell_shape, cover_percent in cells_covering:
            cells_cover_what_polygons[cell_id].append(obj['id'])

    for polygon_cell in polygon_cells:
        polygon_cell['cell_permutations'] = list(possible_cells_for_polygon(polygon_cell['cells'], polygon_cell['num'], cell_neighbours))
        assert len(polygon_cell['cell_permutations']) > 0, "No permutations for this polygon?"
        polygon_cell['cell_permutations_as_set'] = [set(x) for x in polygon_cell['cell_permutations']]

    polygon_cells.sort(key=lambda x: len(x['cell_permutations']))
    polygon_cells = sort_input_shapes_by_touching(polygon_cells)

    # calculate possible global coverage
    for permutation in product_but_prune_dupe_cells(polygon_cells, cell_neighbours, cells):
        cells_for_input_shape = {x['id']: [cells[y] for y in x['cells_results']] for x in permutation}
        cell_ids_for_input_shape = {x['id']: x['cells_results'] for x in permutation}
        yield [ {'id': obj['id'], 'properties': copy.deepcopy(obj['properties']),
                 'shape': obj['shape'], 'cells': cells_for_input_shape[obj['id']],
                 'cell_ids': cell_ids_for_input_shape[obj['id']] }
                for obj in input_shapes ]


def _num_neighbours(list_of_cells, cell_neighbours):
    cells_in_this_list = set(x['cell_id'] for x in list_of_cells)
    total_num_neighbours = 0
    for cell_id in cells_in_this_list:
        neighbours = cell_neighbours[cell_id]
        total_num_neighbours += sum(1 for x in neighbours if x in cells_in_this_list)

    return total_num_neighbours


def match_up_cells_to_polygons_via_permutations(cells, input_shapes):
    results = []
    for possibility in itertools.islice(all_possibilities_for_cell_match_up(cells, input_shapes), 1):
        result = []
        for obj in possibility:
            result.extend([{'properties': copy.deepcopy(obj['properties']), 'shape': obj['cells'][i], 'cell_id':obj['cell_ids'][i]} for i in range(len(obj['cells']))])
        results.append(result)

    assert len(results) > 0
    cell_neighbours = find_neighbours(cells)
    results.sort(key=lambda x, cell_neighbours=cell_neighbours: _num_neighbours(x, cell_neighbours), reverse=True)
    return results[0]


def is_all_one_group(cells, cell_neighbours):
    """Returns true if all the cells in cells touch each other, or are they 1 or more different groups"""
    if len(cells) == 0:
        return True
    unsure_cells = set(cells)
    ok_cells = set()
    assert all(cid in cell_neighbours for cid in unsure_cells)

    ok_cells.add(unsure_cells.pop())

    while len(unsure_cells) > 0:
        # These are unsure cells that are actually OK
        cells_that_touch_ok_cells = {cid for cid in unsure_cells if any(okcellid in cell_neighbours[cid] for okcellid in ok_cells)}
        if len(cells_that_touch_ok_cells) == 0:
            # no more cells touch ok cells, ergo, non-group
            assert len(unsure_cells) > 0
            return False
        else:
            # These cells are OK, move from unsure to OK
            ok_cells.update(cells_that_touch_ok_cells)
            unsure_cells.difference_update(cells_that_touch_ok_cells)

    # Got to here, so it must be OK and all one group
    return True


def number_of_groups(cells, cell_neighbours):
    """
    Return the number of contiguous groups
    """
    if len(cells) == 0:
        return 0

    groups = []
    current_group = set()
    assigned_cells = set()
    unexaminined_cells = set(cells)

    seed_cell = unexaminined_cells.pop()
    current_group.add(seed_cell)

    while len(unexaminined_cells) > 0:

        current_group_neighbours = set.union(*[cell_neighbours[cid] for cid in current_group])

        cells_that_touch_this_group = unexaminined_cells & current_group_neighbours

        if len(cells_that_touch_this_group) == 0:
            # Nothing more touches this group, so create a new group
            groups.append(current_group)
            current_group = set()
            seed_cell = unexaminined_cells.pop()
            current_group.add(seed_cell)
        else:
            unexaminined_cells.difference_update(cells_that_touch_this_group)
            current_group.update(cells_that_touch_this_group)

    groups.append(current_group)
    return len(groups)


def copy_polygons(polygons):
    results = {}
    for pid, polygon in polygons.items():
        new_polygon = {}
        for key in ['id', 'property_to_grid_on']:
            new_polygon[key] = polygon[key]
        new_polygon['cell_ids'] = copy.copy(polygon['cell_ids'])
        results[pid] = new_polygon

    return results

def copy_cell_neighbours(cell_neighbours):
    return {k:copy.copy(cell_neighbours[k]) for k in cell_neighbours}


def contiguous_group_score(polygons, cell_neighbours):
    """
    Given a polygons dict, return a sum of all the unique groups per polygon.
    If all polygons have only contiguous cells, then this will be the number of
    polygons.
    """
    return sum(
        number_of_groups(polygons[polygon]['cell_ids'], cell_neighbours)
        for polygon in polygons)


def contiguous_polygon(polygons, cell_neighbours):
    """Returns 1 if all cells touch each other (i.e. no separate groups), 2 if this is 2 non-touching islands, etc."""
    all_cells_present = set.union(*[set(p['cell_ids']) for p in polygons.values()])
    return number_of_groups(all_cells_present, cell_neighbours)


def overlap_fit(polygons, polygon_cell_overlaps):
    """
    For each polygon, how much do all it's cells overlap the polygon.
    Configurations where cells for a polygon don't overlap a lot will have a
    low score, but configurations where the cells and polygons overlap a lot
    will have a high score
    """
    return sum(sum(polygon_cell_overlaps[pid][cid] for cid in polygons[pid]['cell_ids']) for pid in polygons)


def move_cell_to_this_polygon(polygonid, cellid, polygons):
    """Move cellid from where it is to polygon[polygonid]"""
    polygonid_that_has_it = [pid for pid in polygons if cellid in polygons[pid]['cell_ids']]
    assert len(polygonid_that_has_it) == 1, polygonid_that_has_it
    polygonid_that_has_it = polygonid_that_has_it[0]

    if polygonid_that_has_it == polygonid:
        return polygons
    else:
        new_polygons = copy_polygons(polygons)
        new_polygons[polygonid]['cell_ids'].append(cellid)
        new_polygons[polygonid_that_has_it]['cell_ids'].remove(cellid)
        #print "Moving cellid {} from pid {} to pid {}".format(cellid, polygonid_that_has_it, polygonid)

        return new_polygons


def swap_empty_cell_for_this_cell(polygons, cell_neighbours, total_cell_neighbours, polygonid, empty_cell, nonempty_cell):
    new_polygons = copy_polygons(polygons)
    new_cell_neighbours = copy_cell_neighbours(cell_neighbours)

    new_polygons[polygonid]['cell_ids'].remove(nonempty_cell)
    new_polygons[polygonid]['cell_ids'].append(empty_cell)

    del new_cell_neighbours[nonempty_cell]
    new_cell_neighbours[empty_cell] = copy.copy(total_cell_neighbours[empty_cell]) - {nonempty_cell}

    return new_polygons, new_cell_neighbours


def remove_cells_from_this_polygon(polygonid, cellids, polygons, cell_neighbours):
    """Remove the cell `cellid` from `polygonid`."""
    new_polygons = copy_polygons(polygons)
    new_cell_neighbours = copy_cell_neighbours(cell_neighbours)
    for cellid in cellids:
        new_polygons[polygonid]['cell_ids'].remove(cellid)
        del new_cell_neighbours[cellid]
        new_cell_neighbours = {k:(v - {cellid}) for k, v in new_cell_neighbours.items()}

    return new_polygons, new_cell_neighbours


def remove_cells(cellids, polygons, cell_neighbours):
    """If we don't know what polygon has it, remove it"""
    for cellid in cellids:
        polygon_that_has_it = [pid for pid in polygons if cellid in polygons[pid]['cell_ids']]
        assert len(polygon_that_has_it) == 1
        polygons, cell_neighbours = remove_cells_from_this_polygon(polygon_that_has_it[0], [cellid], polygons, cell_neighbours)

    return polygons, cell_neighbours


def move_cells_from_one_polygon_to_another(polygons, cell_neighbours):
    cellid_to_polygonid = {}
    for polygon in polygons.values():
        cellid_to_polygonid.update({cid: polygon['id'] for cid in polygon['cell_ids']})

    polygon_neighbours = {pid: calculate_polygon_neighbours(pid, polygons, cell_neighbours) for pid in polygons}

    possible_new_options = []
    for polygonid in polygons:
        for neighbourid in polygon_neighbours[polygonid]:
            for cellid in polygons[polygonid]['cell_ids']:
                possible_new_options.append((move_cell_to_this_polygon(neighbourid, cellid, polygons), cell_neighbours))

    return possible_new_options


def under_score(polygons):
    return sum((p['property_to_grid_on'] - len(p['cell_ids'])) for p in polygons.values() if len(p['cell_ids']) < p['property_to_grid_on'])


def num_polygons_below(polygons):
    """Number of polygons which have less then required cells."""
    return sum(1 for p in polygons.values() if len(p['cell_ids']) < p['property_to_grid_on'])




def redistribute_cells_to_correct_number_below(polygons, cells, cell_polygon_overlaps, cell_neighbours):
    """
    Some polygons will have more than the required amount of cells. Correct
    this so that all polygons exactly the correct number of cells.
    """

    total_cell_neighbours = find_neighbours(cells)

    def score_for_reducing_below(polygons, cell_neighbours, total_cell_neighbours, cell_polygon_overlaps):
        # This is the metrics we're using to rank the options
        return (
            contiguous_group_score(polygons, cell_neighbours),
            num_polygons_below(polygons),
            -correct_coverage_percent(polygons, cell_polygon_overlaps),
        )

    polygons, cell_neighbours = make_better_combo(
        (polygons, cells, cell_polygon_overlaps, cell_neighbours, total_cell_neighbours),
        generate_options=move_cells_from_one_polygon_to_another,
        rank_options=lambda new_polygons, new_cell_neighbours, total_cell_neighbours=total_cell_neighbours, cell_polygon_overlaps=cell_polygon_overlaps : score_for_reducing_below(new_polygons, new_cell_neighbours, total_cell_neighbours, cell_polygon_overlaps),
        do_until=lambda polygons: all(len(polygon['cell_ids']) >= polygon['property_to_grid_on'] for polygon in polygons.values()),
    )

    return polygons



def calculate_edge_distance(polygons, cell_neighbours):
    """
    If a polygon has an edge cell, then it has an edge distance of 0. Other
    polygons without an edge distance that don't have edge cells have an edge
    distance of 1, etc.
    """
    max_possible_neighbours = max(len(neighbours) for neighbours in cell_neighbours.values())

    def _is_edge_cell(cellid):
        return len(cell_neighbours[cellid]) < max_possible_neighbours

    # {edge_distance_int: set(polygonids with this edge distance)}
    results = {}

    # edge polygons
    results[0] = {pid for pid in polygons if any(_is_edge_cell(cellid) for cellid in polygons[pid]['cell_ids'])}
    examinined_polygons = set()
    examinined_polygons.update(results[0])
    unexaminined_polygons = set(polygons.keys()) - results[0]
    current_level = 0

    while len(unexaminined_polygons) > 0:
        previous_cells = set.union(*[set(polygons[pid]['cell_ids']) for pid in results[current_level]])
        cells_that_neighbour_this_level = set.union(*[cell_neighbours[cid] for cid in previous_cells])
        polygons_with_these_cells = {p for p in polygons if any(cid in polygons[p]['cell_ids'] for cid in cells_that_neighbour_this_level)}
        polygons_with_these_cells = polygons_with_these_cells - examinined_polygons
        assert len(polygons_with_these_cells) > 0
        current_level += 1
        results[current_level] = polygons_with_these_cells
        examinined_polygons.update(polygons_with_these_cells)
        unexaminined_polygons.difference_update(polygons_with_these_cells)

    return results


def total_neighbour_score(cell_neighbours):
    """
    How many neighbours does this cell_neighbours combo have.

    Big spidly arms will have a low number (since each cell will have a low
    number of cells), but a blob will have a high number.
    This also measures holes. lower number = more holes.
    """

    return sum(len(cell_neighbours[cid]) for cid in cell_neighbours)


def calculate_polygon_neighbours(polygonid, polygons, cell_neighbours):
    """Return a set of polygon ids which neighbour this polygonid."""
    cellids = polygons[polygonid]['cell_ids']
    neighbour_cells = set.union(*[set(cell_neighbours[cid]) for cid in cellids])
    neighbour_cells.difference_update(cellids)
    neighbour_polygons = {pid for pid in polygons if any(cid in polygons[pid]['cell_ids'] for cid in neighbour_cells)}
    neighbour_polygons.discard(polygonid)  # just in case

    return neighbour_polygons


def correct_coverage_percent(polygons, cell_polygon_overlaps):
    return sum(sum(cell_polygon_overlaps[cid][polygon['id']] for cid in polygon['cell_ids']) for polygon in polygons.values())


def make_better_combo((polygons, cells, cell_polygon_overlaps, cell_neighbours, total_cell_neighbours), generate_options, rank_options, do_until):

    while True:
        possible_new_options = []

        possible_new_options.extend(generate_options(polygons, cell_neighbours))

        possible_new_options = [(
            rank_options(new_polygons, new_cell_neighbours, total_cell_neighbours, cell_polygon_overlaps),
            (new_polygons, new_cell_neighbours)
            ) for new_polygons, new_cell_neighbours in possible_new_options]
        possible_new_options.sort(key=lambda x: x[0])

        if len(possible_new_options) > 0:
            polygons, cell_neighbours = possible_new_options[0][-1]
        else:
            # There is nothing to do
            raise Exception("No options, cannot fix.")

        if do_until(polygons):
            # We have finished
            break

    return polygons, cell_neighbours


def delete_cell_options(polygons, cell_neighbours):
    cells_deletable = [{cellid for cellid in polygons[pid]['cell_ids']} for pid in polygons if len(polygons[pid]['cell_ids']) > polygons[pid]['property_to_grid_on']]
    if len(cells_deletable) == 0:
        return []
    cells_deletable = set.union(*cells_deletable)

    possible_new_options = []
    for possible_edge_cell in cells_deletable:
        # What would be polygons and cell_neighbours after removing this
        new_polygons, new_cell_neighbours = remove_cells([possible_edge_cell], polygons, cell_neighbours)

        possible_new_options.append((new_polygons, new_cell_neighbours))

    return possible_new_options

def redistribute_cells_to_correct_number_above(polygons, cells, cell_polygon_overlaps, cell_neighbours):
    """
    Some polygons will have more than the required amount of cells. Correct
    this so that all polygons exactly the correct number of cells.
    """
    # these are polygons we've fixed already. keep track so we don't get into
    # an endless loop

    polygons_not_to_steal_from = set()
    total_cell_neighbours = find_neighbours(cells)

    polygons, cell_neighbours = make_better_combo(
        (polygons, cells, cell_polygon_overlaps, cell_neighbours, total_cell_neighbours),
        generate_options=delete_cell_options,
        rank_options=lambda new_polygons, new_cell_neighbours, total_cell_neighbours=total_cell_neighbours, cell_polygon_overlaps=cell_polygon_overlaps : score_for_combination(new_polygons, new_cell_neighbours, total_cell_neighbours, cell_polygon_overlaps),
        do_until=lambda polygons: all(len(polygon['cell_ids']) == polygon['property_to_grid_on'] for polygon in polygons.values()),
    )

    # FIXME this should be zero
    diff_per_polygon = {polygonid: (len(polygon['cell_ids']) - polygon['property_to_grid_on']) for polygonid, polygon in polygons.items()}

    # What polygons have less than the required amount
    polygons_above = [(diff_per_polygon[polygonid], polygonid) for polygonid in list(diff_per_polygon.keys()) if diff_per_polygon[polygonid] > 0]
    print("There are {0:3d} polygons overserved with total of {1:3} cells over".format(len(polygons_above), sum(x[0] for x in polygons_above)))

    return polygons

def empty_group_score(polygons, total_cell_neighbours):
    """
    1 means all empty cells are in one group, i.e. no holes. 2 means there is one hole.
    """
    empty_cells = set(total_cell_neighbours.keys()) - set.union(*[set(polygon['cell_ids']) for polygon in polygons.values()])
    return number_of_groups(empty_cells, total_cell_neighbours)


def score_for_combination(polygons, cell_neighbours, total_cell_neighbours, cell_polygon_overlaps):
    # This is the metrics we're using to rank the options
    return (
        contiguous_polygon(polygons, cell_neighbours),
        contiguous_group_score(polygons, cell_neighbours),
        empty_group_score(polygons, total_cell_neighbours),
        -correct_coverage_percent(polygons, cell_polygon_overlaps),
        -total_neighbour_score(cell_neighbours),
    )



def redistribute_cells_to_make_better_shapes(polygons, cells, cell_polygon_overlaps, cell_neighbours):
    """Move some cells around so that the shapes are bit nicer"""

    # This will include empty cells and not change with moving things around.
    total_cell_neighbours = find_neighbours(cells)


    while True:
        # We have several options to do
        # (a) Move a cell to an empty cell
        # (b) swap 2 cells in 2 neighbouring polygons
        # We calculate all permutations, and then see if any has a better score
        # than what we have now, if so we use that. If we don't, then we
        # finish. this means we iteratively try to improve the combination

        actions = {}

        current_score = score_for_combination(polygons, cell_neighbours, total_cell_neighbours, cell_polygon_overlaps)
        current_polygons = polygons
        current_cell_neighbours = cell_neighbours
        possible_new_options = []

        # do stuff
        empty_cells = set(range(len(cells))) - set.union(*[set(polygon['cell_ids']) for polygon in polygons.values()])
        for empty_cell in empty_cells:
            neighbour_cells = total_cell_neighbours[empty_cell]
            neighbour_polygon_ids = {pid for pid, polygon in polygons.items() if any(neighbour_cell in polygon['cell_ids'] for neighbour_cell in neighbour_cells)}
            for neighbour_polygon_id in neighbour_polygon_ids:
                for cell in polygons[neighbour_polygon_id]['cell_ids']:
                    # Make this cell empty and make the original empty cell be
                    # this one
                    action = ('swapempty', empty_cell, cell)
                    actions[action] = swap_empty_cell_for_this_cell(polygons, cell_neighbours, total_cell_neighbours, neighbour_polygon_id, empty_cell, cell)
                    possible_new_options.append(action)

        possible_new_options = [(
            score_for_combination(actions[action][0], actions[action][1], total_cell_neighbours, cell_polygon_overlaps),
            action
            ) for action in possible_new_options]
        # add current combo in
        possible_new_options.append((current_score, None))
        possible_new_options.sort(key=lambda x: x[0])
        print("Optimizating: There are {} combinations".format(len(possible_new_options)))

        best = possible_new_options[0][1]
        if best is None:
            # means current option is best
            print("Finished optimizing")
            break
        else:
            polygons, cell_neighbours = actions[best]

    return polygons


def redistribute_cells_for_correct_number(polygons, cells, cell_polygon_overlaps, cell_neighbours):
    assert len(cells) >= len(polygons)

    print "Fixing below's"
    polygons = redistribute_cells_to_correct_number_below(polygons, cells, cell_polygon_overlaps, cell_neighbours)
    assert all(len(p['cell_ids']) >= p['property_to_grid_on'] for p in polygons.values()), [p for p in polygons.values() if len(p['cell_ids']) < p['property_to_grid_on']]

    print "Fixing aboves's"
    polygons = redistribute_cells_to_correct_number_above(polygons, cells, cell_polygon_overlaps, cell_neighbours)
    assert all(len(p['cell_ids']) == p['property_to_grid_on'] for p in polygons.values())

    polygons = redistribute_cells_to_make_better_shapes(polygons, cells, cell_polygon_overlaps, cell_neighbours)

    # recreate the 'cells' attribute based on the 'cell_ids'
    for obj in polygons.values():
        obj['cells'] = [cells[cid] for cid in obj['cell_ids']]

    return polygons


def match_up_cells_to_polygons_via_largest_owner(cells, input_shapes, property_to_grid_on, keep_empty_cells=False):
    assert len(cells) >= len(input_shapes), "not enough cells"
    cell_polygon_overlaps = {cellid: {obj['id']: intersection_percent(cells[cellid], obj['shape']) for obj in input_shapes} for cellid in range(len(cells))}
    cell_neighbours = find_neighbours(cells)
    all_cell_ids = set(range(len(cells)))

    cells_in_polygon = defaultdict(set)
    for cellid, cell in enumerate(cells):
        largest_polygon_coverage = sorted(
                [(percent, polygonid) for (polygonid, percent) in cell_polygon_overlaps[cellid].items()],
                reverse=True)[0][1]
        cells_in_polygon[largest_polygon_coverage].add(cellid)

    for obj in input_shapes:
        obj['cell_ids'] = list(cells_in_polygon[obj['id']])
        obj['cells'] = [cells[cellid] for cellid in obj['cell_ids']]

    # create a polygons list which can be easily copied
    polygons = {obj['id']: {
                'id': obj['id'], 'cell_ids': obj['cell_ids'],
                'property_to_grid_on': obj['property_to_grid_on']}
                for obj in input_shapes}

    # Fixes the polygon count
    polygons = redistribute_cells_for_correct_number(polygons, cells, cell_polygon_overlaps, cell_neighbours)

    result = []

    kept_cells = set()
    for obj in input_shapes:
        pid = obj['id']  # polygon id
        assert pid != -1, "We are usign -1 as a sentinal for empty cells"
        for i in range(len(polygons[pid]['cells'])):
            properties = copy.deepcopy(obj['properties'])
            if keep_empty_cells:
                properties['polygon_id'] = pid
                properties['orig_pid'] = pid
            kept_cells.add(polygons[pid]['cell_ids'][i])
            result.append(
                    {'properties': properties, 'shape': polygons[pid]['cells'][i],
                    'cell_id': polygons[pid]['cell_ids'][i]}
            )

    property_keys = result[0]['properties'].keys()
    if keep_empty_cells:
        for empty_cell_id  in list(all_cell_ids - kept_cells):
            properties = {}
            properties.update({key: '' for key in property_keys})
            properties['polygon_id'] = -1
            properties['orig_pid'] = -1
            result.append(
                    {'properties': properties, 'shape': cells[empty_cell_id],
                    'cell_id': empty_cell_id}
            )

    confirm_cells_have_correct_numbers(result, property_to_grid_on)


    return result


def add_unique_cell_id_to_results(objects):
    polygon_cell_counter = defaultdict(int)

    for o in objects:
        polygon_id = o['properties']['polygon_id']
        o['properties']['cell_id'] = "%s_%s" % (polygon_id, polygon_cell_counter[polygon_id])
        polygon_cell_counter[polygon_id] += 1

    return objects


def grid(input_objects, property_to_grid_on, keep_empty_cells=False, include_unique_cell_id=False):
    """Grid this set of input_objects based on property_to_grid_on."""
    objects = match_up_property(input_objects, property_to_grid_on)

    total_values = int(sum(x['property_to_grid_on'] for x in objects))

    densities = [x['shape'].area/x['property_to_grid_on'] for x in objects]
    avg_density = mean(densities)
    bounds = get_bbox(input_objects)

    cells = cover_with_hexagons(bounds, avg_density)
    cells = remove_non_overlapping(total_values, cells, objects)

    #cells = match_up_cells_to_polygons_via_permutations(cells, objects)
    cells = match_up_cells_to_polygons_via_largest_owner(cells, objects, property_to_grid_on, keep_empty_cells)

    if include_unique_cell_id:
        cells = add_unique_cell_id_to_results(cells)

    return cells

def parse_args(args):
    parser = argparse.ArgumentParser(description='')
    parser.add_argument("-i", "--input")
    parser.add_argument("-o", "--output")
    parser.add_argument("-p", "--property-to-grid-on")

    parser.add_argument("--do-manual-touchup", action="store_true")
    parser.add_argument("--cleanup-manual-touchup", action="store_true")
    parser.add_argument("--match-up-csv")
    parser.add_argument("--csv-file")

    parser.add_argument("--include-unique-cell-id", action="store_true")

    args = parser.parse_args(args)

    return args


def post_processing_cleanup(objects, property_to_grid_on, include_unique_cell_id=False):
    # TODO make this more functional and copy objects ?

    # create 'polygon_id' to properties dict
    pid_to_properties = {}
    for o in objects:
        if o['properties']['orig_pid'] not in pid_to_properties:
            properties = copy.copy(o['properties'])
            del properties['polygon_id']
            del properties['orig_pid']
            pid_to_properties[o['properties']['orig_pid']] = properties

    # for objects that have changed, set the properties
    for o in objects:
        if o['properties']['orig_pid'] != o['properties']['polygon_id']:
            o['properties'].update(pid_to_properties[o['properties']['polygon_id']])

    # remove the (now) empty cells
    objects = [o for o in objects if o['properties']['polygon_id'] != -1]

    confirm_cells_have_correct_numbers(objects, property_to_grid_on)

    if include_unique_cell_id:
        # Need to do this while we have the polygon_id property
        objects = add_unique_cell_id_to_results(objects)

    # remove our temporary tracking properties
    for o in objects:
        del o['properties']['polygon_id']
        del o['properties']['orig_pid']

    return objects


def confirm_cells_have_correct_numbers(objects, property_to_grid_on):
    # confirm each polygon has enough cells to confirm user hasn't made
    # mistake
    num_cells_per_polygon = defaultdict(int)
    num_required_per_polygon = defaultdict(set)
    for o in objects:
        num_cells_per_polygon[o['properties']['polygon_id']] += 1
        num_required_per_polygon[o['properties']['polygon_id']].add(o['properties'][property_to_grid_on])

    # Remove sentinal values
    if -1 in num_required_per_polygon:
        # There are empty cells here, don't examine them, since they aren't
        # real polygons
        del num_required_per_polygon[-1]
        del num_cells_per_polygon[-1]

    if any(len(num_required) > 1 for num_required in num_required_per_polygon.values()):
        # Someone's been editing the property_to_grid_on and there are at least
        # 2 rows with the same polygon_id but different property_to_grid_on
        raise Exception("bad " + property_to_grid_on)
    num_required_per_polygon = {pid: value.pop() for pid, value in num_required_per_polygon.items()}

    invalid_polygons = [pid for pid in num_cells_per_polygon if num_cells_per_polygon[pid] != num_required_per_polygon[pid]]

    if len(invalid_polygons) != 0:
        for invalid_polygon in invalid_polygons:
            print "Polygon id {} has {} cells but needs exactly {}".format(invalid_polygon, num_cells_per_polygon[invalid_polygon], num_required_per_polygon[invalid_polygon])
        # Missing cells
        raise Exception("Missing cells")


def match_up_csv(objects, csv_data, match_up_csv_properties):
    polygon_col, csv_col = match_up_csv_properties.split(":", 1)

    # input validation
    # confirm correct property names
    assert all(polygon_col in obj['properties'] for obj in objects)
    assert all(csv_col in row for row in csv_data)

    # Are there enough polygons for all the ones in each
    assert len(objects) == len(csv_data)
    polygons_per_property = defaultdict(list)
    for obj in objects:
        polygons_per_property[obj['properties'][polygon_col]].append(obj)
    csv_rows_per_property = defaultdict(list)
    for row in csv_data:
        csv_rows_per_property[row[csv_col]].append(row)

    # check it can all add up
    missing_from_csv = set(polygons_per_property.keys()).difference(csv_rows_per_property.keys())
    missing_from_polygons = set(csv_rows_per_property.keys()).difference(polygons_per_property.keys())
    assert len(missing_from_csv) == 0, missing_from_csv
    assert len(missing_from_polygons) == 0, missing_from_polygons
    for key in polygons_per_property.keys():
        assert len(polygons_per_property[key]) == len(csv_rows_per_property[key])



    import pdb ; pdb.set_trace()
    return objects



def main(argv):
    args = parse_args(argv)
    objects, fileformat_meta = open_input_source(args.input)
    confirm_all_input_geoms_valid(objects)
    if args.do_manual_touchup:
        output = grid(objects, args.property_to_grid_on, keep_empty_cells=True)
        fileformat_meta['schema']['properties']['polygon_id'] = 'int'
        fileformat_meta['schema']['properties']['orig_pid'] = 'int'
    elif args.cleanup_manual_touchup:
        # remove the empty cells
        output = post_processing_cleanup(objects, args.property_to_grid_on, include_unique_cell_id=args.include_unique_cell_id)
        del fileformat_meta['schema']['properties']['polygon_id']
        del fileformat_meta['schema']['properties']['orig_pid']
    elif args.match_up_csv is not None:
        with open(args.csv_file) as fp:
            csv_data = list(csv.DictReader(fp))
        output = match_up_csv(objects, csv_data, args.match_up_csv)
    elif not arg.do_manual_touchup and not args.cleanup_manual_touchup:
        # want to do it all in one go, no manual touchup / empty calls
        output = grid(objects, args.property_to_grid_on, keep_empty_cells=False, include_unique_cell_id=args.include_unique_cell_id)
    else:
        raise NotImplementedError()

    if args.include_unique_cell_id:
        fileformat_meta['schema']['properties']['cell_id'] = 'str'

    write_shapefile(args.output, convert_objects_to_geojson_geometry(output), fileformat_meta)


if __name__ == '__main__':
    #main(['-i', 'irish-constituancies-warped.shp', '-o', 'irish-constituancies-w-empty.shp', '-p', 'NO_MMB_NUM', '--do-manual-touchup'])
    #main(['-i', 'irish-constituancies-reallocated.shp', '-o', 'irish-constituancies-cartogram.shp', '-p', 'NO_MMB_NUM', '--cleanup-manual-touchup', '--include-unique-cell-id'])
    #main(['-i', 'us-electoral-college/us-electoral-college2.shp', '-o', 'us-electoral-college/cartogram-for-fixup.shp', '-p', 'Electoral', '--do-manual-touchup'])
    #main(['-i', 'us-electoral-college/cartograme-reallocated.shp', '-o', 'us-electoral-college/cartogram.shp', '-p', 'Electoral', '--cleanup-manual-touchup'])
    main(['-i', 'irish-constituancies-cartogram.shp', '-o', 'irish-constituancies-members.shp', '--csv-file', 'members.csv', '--match-up-csv', 'NAME:Constituency'])
