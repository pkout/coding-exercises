# l must be sorted
def binary_search_recursive(l, v):
    mid_idx = len(l) // 2
    mid = l[mid_idx]

    if v == mid:
        return 'Found'

    if len(l) == 1:
        return 'Not Found'

    if v < mid:
        return binary_search_recursive(l[:mid_idx], v)

    if v > mid:
        return binary_search_recursive(l[mid_idx:], v)

    return 'Not Found'

print(binary_search_recursive([1, 3, 5, 7, 9], 5))


def binary_search_recursive2(l, v, start=None, end=None):
    start = 0 if start is None else start
    end = len(l) if end is None else end
    mid = (start + end) // 2

    if start > end:
        return -1

    if l[mid] == v:
        return mid

    if v < l[mid]:
        return binary_search_recursive2(l, v, start, mid - 1)

    if v > l[mid]:
        return binary_search_recursive2(l, v, mid + 1, end)

print(binary_search_recursive2([1, 3, 5, 7, 9, 10], 5))


def binary_search_loop2(l, v):
    start = 0
    end = len(l)

    while start <= end:
        mid = (start + end) // 2

        if v == l[mid]:
            return mid

        if v < l[mid]:
            end = mid - 1

        if v > l[mid]:
            start = mid + 1

    if start > end:
        return -1

    return l[mid]

print(binary_search_loop2([1, 3, 5, 7, 9, 10], 3))
