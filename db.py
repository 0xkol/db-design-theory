"""
Implementations of algorithms in design theory.
Author: Moshe Kol
"""

from typing import FrozenSet, Set, Iterable, List
from queue import Queue
from itertools import combinations, chain


def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


class FD:
    """ Represent a Functional Dependency X->Y where X and Y are sets of attributes. """
    def __init__(self, lhs: Iterable[str], rhs: Iterable[str]):
        self.X = frozenset(lhs)
        self.Y = frozenset(rhs)

    def __repr__(self):
        return ''.join(self.X) + '->' + ''.join(self.Y)

    @staticmethod
    def parse(fd: str):
        result = fd.split('->')
        if len(result) != 2:
            raise ValueError('Cannot parse ' + fd + ' into a correct FD.')
        return FD(result[0], result[1])


def make_fd_set(*args) -> Set[FD]:
    """ A convinient function that return a set of functional dependencies.
    Argument can be FD or a string (in this case, it is parsed). """
    result = set()
    for arg in args:
        if type(arg) is str:
            result.add(FD.parse(arg))
        elif type(arg) is FD:
            result.add(arg)
        else:
            raise TypeError('argument ' + arg + ' must be of type str or FD.')
    return result


def closure(X: Set[str], F: Set[FD]) -> Set[str]:
    """ Compute X+ with respect to set of FD's F.
    i.e. Return a set of all attibutes A such that X->A follows from F. """
    prev, curr = set(), set(X)
    while prev < curr:
        prev = set(curr)
        for fd in F:
            if fd.X <= curr:
                curr |= fd.Y
    return prev


def minimize(X: Set[str], F: Set[FD]) -> FrozenSet[str]:
    """ Return a set Z<=X of attributes with the propery:
        if A in Z then A is not in (Z-A)+ (closure w.r.t. F).
        i.e. we cannot remove any attribute from Z without "violating" closure.
    """
    Z = set(X)
    for A in X:
        if A in closure(Z-{A}, F):
            Z -= {A}
    return frozenset(Z)


def find_key(R: Set[str], F: Set[FD]) -> FrozenSet[str]:
    """ Return a single key for relation R w.r.t FD set denoted by F. """
    return frozenset(minimize(R, F))


def find_all_keys(R: Set[str], F: Set[FD]) -> Set[FrozenSet[str]]:
    """ Return a set of all keys for relation R w.r.t the FD set denoted by F. """
    initial_key = find_key(R, F)
    keys = {initial_key}
    queue = Queue()
    queue.put(initial_key)
    while not queue.empty():
        key = queue.get()
        for fd in F:
            if fd.Y & key:
                skey = fd.X | (key - fd.Y)  # skey is a super key
                if not any(k for k in keys if k <= skey):
                    skey_minimized = minimize(skey, F)
                    keys.add(skey_minimized)
                    queue.put(skey_minimized)
    return keys


def print_all_keys(R: Set[str], F: Set[FD]):
    """ Printing a comma seperated list of keys for the relation R with
    respect to the set of FDs denoted by F. """
    all_keys = find_all_keys(R, F)
    print(', '.join(''.join(sorted(key)) for key in all_keys))


def minimal_cover(F: Set[FD]) -> Set[FD]:
    """ Return an equivalent set of FD's which is minimal:
        1. Every right side of dependency in F is a single attribute.
        2. For no X->A in F and proper subset Z of X is F-{X->A}|{Z->A} equivalent to F.
        3. For no X->A in F is the set F-{X->A} equivalent to F.
    """
    G = set()

    # Step 1: Every right side of dependency in F is a single attribute.
    for fd in F:
        for A in fd.Y:
            G.add(FD(fd.X, A))

    # Step 2: For no X->A in F and proper subset Z of X is F-{X->A}|{Z->A} equivalent to F.
    for fd in set(G):
        minimized_rhs = minimize(fd.X, G)
        if minimized_rhs < fd.X:
            G.add(FD(minimized_rhs, fd.Y))
            G.remove(fd)

    # Step 3: For no X->A in F is the set F-{X->A} equivalent to F.
    for fd in set(G):
        if fd.Y <= closure(fd.X, G-{fd}):
            G.remove(fd)

    return G


def is_dependency_preserving(decomosition: List[Set[str]], F: Set[FD]) -> bool:
    """ Return True iff the given decomposition preserve dependencies of F. """
    for fd in F:
        prev, curr = set(), set(fd.X)
        while prev < curr:
            prev = set(curr)
            for relation in decomosition:
                curr |= closure(curr & relation, F) & relation
        if not (fd.Y <= curr):
            return False
    return True


def _project(R: Set[str], F: Set[FD]) -> Set[FD]:
    """ Compute the projection of F onto R. """
    PF = set()
    for X in powerset(R):
        PF.add(FD(X, closure(X, F) & R))
    return PF


def project(R: Set[str], F: Set[FD]) -> Set[FD]:
    """ Compute the projection of F onto R. Returns a minimal FD set. """
    return minimal_cover(_project(R, F))


def is_bcnf(R: Set[str], F: Set[FD]) -> bool:
    """ Return True iff the given schema R is in BCNF w.r.t. F. """
    for fd in F:
        if not (fd.Y <= fd.X or closure(fd.X, F) == R):
            print('[is_bcnf] ', fd, ' violates BCNF for schema ', R, ' and set ', F)
            return False
    return True


def is_bcnf_decomposition(decomosition: List[Set[str]], F: Set[FD]) -> bool:
    """ Return True iff each sub-schema R in the decomposition is in BCNF with
    respect to projection of F onto R. """
    return all(is_bcnf(R, project(R, F)) for R in decomosition)


def _find_bcnf_decomposition(R: Set[str], F: Set[FD]) -> List[Set[str]]:
    """ Return a list of sub-schemas each of which in BCNF w.r.t. the projection
    of F onto the sub-schema. Moreover, the decomposition is lossless-join. """
    for fd in F:
        if not (fd.Y <= fd.X or closure(fd.X, F) == R):
            R1 = closure(fd.X, F)
            R2 = fd.X | (R - R1)
            decomp1 = _find_bcnf_decomposition(R1, project(R1, F))
            decomp2 = _find_bcnf_decomposition(R2, project(R2, F))
            return decomp1 + decomp2
    return [R]


def find_bcnf_decomposition(R: Set[str], F: Set[FD]) -> List[str]:
    """ Same as _find_bcnf_decomposition but return the decomposition in a
    human readable format. """
    decomposition = _find_bcnf_decomposition(R, F)
    assert(is_bcnf_decomposition(decomposition, F))
    return list(map(lambda d: ''.join(d), decomposition))


def is_3nf(R: Set[str], F: Set[FD]) -> bool:
    """ Return True iff the given schema R is in 3NF w.r.t. F. """
    keys = find_all_keys(R, F)
    for fd in F:
        if not (closure(fd.X, F) == R):
            for A in fd.Y:
                if not (A in fd.X or any(k for k in keys if A in k)):
                    print('[is_3nf] ', fd, A, ' violates 3NF for schema ', R, ' and set ', F)
                    return False
    return True


def is_3nf_decomposition(decomosition: List[Set[str]], F: Set[FD]) -> bool:
    """ Return True iff each sub-schema R in the decomposition is in 3NF with
    respect to projection of F onto R. """
    return all(is_3nf(R, project(R, F)) for R in decomosition)


def find_3nf_decomposition(R: Set[str], F: Set[FD]) -> List[str]:
    """ Return a list of sub-schemas each of which in 3NF w.r.t. the projection
    of F onto the sub-schema. Moreover, the decomposition is lossless-join and
    dependency preserving. """
    keys = find_all_keys(R, F)
    F_min = minimal_cover(F)
    decomposition = [fd.X | fd.Y for fd in F_min]
    if not any(R for R in decomposition for k in keys if k <= R):
        decomposition.append(next(k for k in keys))
    return decomposition
