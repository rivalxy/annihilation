import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Lattice.Nat

/-!
---
title: Annihilation number
type: definition
---
Let $G$ be a finite simple graph with $n$ vertices and $m$ edges, and let
$d_1 \le d_2 \le \dots \le d_n$ be its vertex degrees listed in nondecreasing
order. The *annihilation number* $a(G)$ is the largest integer $k$ with
$0 \le k \le n$ such that
$$
\sum_{i=1}^{k} d_i \le m,
$$
that is, the largest $k$ for which the $k$ smallest degrees sum to at most the
number of edges. The value $k = 0$ always qualifies, so $a(G)$ is well defined.

The annihilation number was originally defined through a reduction process on
the degree sequence; the definition above is an equivalent characterization and
is the one in common use.
-/

namespace Lax421170.AnnihilationNumber

/-- The degrees of the vertices of `G`, listed in nondecreasing order. -/
def degreeSequence {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≤ ·)

/-- The largest `k ≤ n` such that the first `k` entries of the nondecreasing degree
sequence, i.e. the `k` smallest degrees, sum to at most the number of edges. -/
noncomputable def annihilationNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sSup {k : ℕ | k ≤ Fintype.card V ∧ ((degreeSequence G).take k).sum ≤ G.edgeFinset.card}

end Lax421170.AnnihilationNumber
