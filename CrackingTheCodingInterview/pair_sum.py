# Time: O(n)
# Space: O(1)
def pair_sum(n):
    total = 0

    for i in range(n - 1):
        total += sum_pair(i, i + 1)

    return total

def sum_pair(a, b):
    return a + b

print(pair_sum(5))
