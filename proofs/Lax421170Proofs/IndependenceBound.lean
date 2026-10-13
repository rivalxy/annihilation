import Lax421170.IndependenceBound
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Lax421170Proofs

open Finset Lax421170.AnnihilationNumber

/-- In a nondecreasing list `l`, the first `#t` entries sum to at most the sum of any
sub-multiset `t` of `l`. -/
theorem sum_take_card_le_sum {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) :
    ∀ t : Multiset ℕ, t ≤ (l : Multiset ℕ) → (l.take (Multiset.card t)).sum ≤ t.sum := by
  induction l with
  | nil =>
    intro t ht
    simp [Multiset.le_zero.mp (by simpa using ht)]
  | cons a l ih =>
    intro t ht
    rw [List.pairwise_cons] at hl
    by_cases ha : a ∈ t
    · have hle : t.erase a ≤ (l : Multiset ℕ) := by
        simpa using Multiset.erase_le_erase a ht
      have key := ih hl.2 _ hle
      rw [← Multiset.cons_erase ha]
      simpa using key
    · have hle : t ≤ (l : Multiset ℕ) := (Multiset.le_cons_of_notMem ha).mp (by simpa using ht)
      refine le_trans ?_ (ih hl.2 t hle)
      have hlen : Multiset.card t ≤ l.length := by
        simpa using Multiset.card_le_card hle
      rcases hc : Multiset.card t with _ | c
      · simp
      · rw [hc] at hlen
        rw [List.take_succ_cons, List.sum_cons, List.sum_take_succ _ _ hlen]
        have := hl.1 (l[c]'hlen) (List.getElem_mem hlen)
        omega

/-- The degrees of the vertices of an independent set sum to at most the number of edges. -/
theorem sum_degree_le_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Finset V} (hs : G.IsIndepSet s) :
    ∑ v ∈ s, G.degree v ≤ #G.edgeFinset := by
  simp_rw [← G.card_incidenceFinset_eq_degree]
  rw [← card_biUnion]
  · apply card_le_card
    intro e he
    obtain ⟨v, -, hv⟩ := mem_biUnion.mp he
    exact G.incidenceFinset_subset v hv
  · intro v hv w hw hvw
    rw [Function.onFun, ← disjoint_coe]
    simp only [SimpleGraph.coe_incidenceFinset]
    rw [Set.disjoint_iff_inter_eq_empty]
    exact G.incidenceSet_inter_incidenceSet_of_not_adj (hs hv hw hvw) hvw

/--
---
conclusion: Lax421170.IndependenceBound.indepNum_le_annihilationNumber
---
Let $S$ be a maximum independent set, so $|S| = \alpha(G)$. Since no edge has
both endpoints in $S$, every edge is incident to at most one vertex of $S$, and
hence $\sum_{v \in S} d(v) \le m$. The $\alpha(G)$ smallest degrees sum to at
most the degrees of any $\alpha(G)$ vertices, in particular of those in $S$.
Therefore $\sum_{i=1}^{\alpha(G)} d_i \le m$, and $\alpha(G) \le a(G)$ by the
maximality in the definition of $a(G)$.
-/
theorem indepNum_le_annihilationNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.indepNum ≤ annihilationNumber G := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  refine le_csSup ⟨Fintype.card V, fun k hk => hk.1⟩ ⟨?_, ?_⟩
  · rw [← hs.card_eq]
    exact card_le_univ s
  · have hsub : s.val.map (fun v => G.degree v) ≤ Finset.univ.val.map (fun v => G.degree v) :=
      Multiset.map_le_map (val_le_iff.mpr (subset_univ s))
    have key := sum_take_card_le_sum (Multiset.pairwise_sort (univ.val.map fun v => G.degree v) (· ≤ ·))
      (s.val.map fun v => G.degree v) (by rw [Multiset.sort_eq]; exact hsub)
    rw [Multiset.card_map, card_val, hs.card_eq] at key
    refine key.trans ?_
    rw [← Finset.sum_eq_multiset_sum]
    exact sum_degree_le_card_edgeFinset G hs.isIndepSet

end Lax421170Proofs
