# Recursive
# Time: O(n)
# Space: O(n)
def sum_recursive(n):
    if n < 1:
        return 0

    return n + sum_recursive(n - 1)

print(sum_recursive(5))


# Loop
# Time: O(n)
# Space: O(1)
def sum_loop(n):
    total = 0

    while n > 0:
        total += n
        n -= 1

    return total

print(sum_loop(5))
