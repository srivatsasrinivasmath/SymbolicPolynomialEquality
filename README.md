This is a haskell project that contains the main computations for a proof that the longest arithmetic progression that is a subset of a geometric progression $(\xi^i)_{i \in \mathbb{N}}, \xi \in \mathbb{C}$ is only $3$, unless $|\xi| = 1$.

A more detailed proof and explanation will be uploaded sometime around Christmas, when I have some time to make it pretty. 

The main function is `mkTest1` contained in the file Monomials.hs. `mkTest1` accepts a list of coefficients $[o_i]$ of length $l$ and tests whether there exists $m,n,[k_i]$ such that 

$$(x^n - 2x^m + 1)(x^n - 2x^{n-m} + 1) =
(\sum_{i = 1}^l o_i x^{k_i})
(\sum_{i = 1}^l o_{l-i} x^{k_i})
$$
