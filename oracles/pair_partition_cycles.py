"""Independent perfect-matching oracle for the even-cycle top coefficient."""
from math import factorial


def full_support_pairings(k):
    if not 2 <= k <= 7:
        raise ValueError('bounded exact oracle requires 2 <= k <= 7')
    size = 2 * k
    mate = [-1] * size

    def simple():
        # A proper interval closes iff all its partners also lie inside it.
        # This uses neither XOR vertices nor a visited-vertex set.
        for start in range(size):
            for stop in range(start + 2, size + 1, 2):
                if start == 0 and stop == size:
                    continue
                if all(start <= mate[i] < stop for i in range(start, stop)):
                    return False
        return True

    def match():
        try:
            first = mate.index(-1)
        except ValueError:
            return int(simple())
        count = 0
        for other in range(first + 1, size):
            if mate[other] == -1:
                mate[first], mate[other] = other, first
                count += match()
                mate[first] = mate[other] = -1
        return count

    return match()


def coefficient(k):
    numerator = 2**k * factorial(k) * full_support_pairings(k)
    value, remainder = divmod(numerator, 4*k)
    assert remainder == 0
    return value
