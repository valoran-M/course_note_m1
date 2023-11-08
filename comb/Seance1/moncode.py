from sage.all import matrix, GF

def response(question: str) -> int:
    """
    Renvoie 42, pour toute question

    EXAMPLES::

        sage: response("Quelle est la réponse à ... et le reste?")
        42

    Complexité: `O(1)`
    """
    return 42

def reduced_echelon_form(m: matrix) -> matrix:
    """
    Renvoie la matrice `m` mise sous forme échelon 
    """
    i = 0
    j = 0
    while j < m.ncols() and i < m.nrows():
        # get first line with an element != 0 in the j column
        l = -1
        for k in range(i, m.nrows()):
            if m[k][j] != 0:
                l = k
                break

        if l == -1:
            j += 1
        else:
            m[i], m[l] = m[l], m[i]
            for k in range(i + 1, m.nrows()):
                if m[k][j] != 0:
                    m[k] = m[k] * m[i][j] - m[i] * m[k][j]
            i += 1
            j += 1

def subspace_membership(V, w):
    """
    Test whether `w` is generated by the vectors in `V`.
    """
    return True
