import Lax421170.AnnihilationNumber
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
---
title: The independence number is at most the annihilation number
type: theorem
---
For every finite simple graph $G$,
$$
\alpha(G) \le a(G),
$$
where $\alpha(G)$ is the independence number of $G$, the largest number of
pairwise nonadjacent vertices, and $a(G)$ is the annihilation number of $G$.

In Lean, $\alpha(G)$ is mathlib's `SimpleGraph.indepNum`, defined as the
supremum of all $k$ for which $G$ has an independent set of exactly $k$
vertices.
-/

namespace Lax421170.IndependenceBound

open Lax421170.AnnihilationNumber

/-- The independence number of a finite simple graph is at most its annihilation number. -/
axiom indepNum_le_annihilationNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.indepNum ≤ annihilationNumber G

end Lax421170.IndependenceBound
