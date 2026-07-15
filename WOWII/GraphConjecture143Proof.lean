import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
Development of a proof of WOWII Graph Conjecture 143.

The proof splits into:
1. acyclic graphs;
2. cyclic graphs with second-smallest degree at least two;
3. the exceptional case where the second-smallest degree is one.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma induce_pair_isTree_of_adj {G : SimpleGraph α} {u v : α} (huv : G.Adj u v) :
    (G.induce ({u, v} : Set α)).IsTree := by
  refine ⟨induce_pair_connected_of_adj huv, ?_⟩
  intro z p hp
  have hnon : ¬p.Nil := hp.not_nil
  have hs := p.adj_snd hnon
  have ht := p.adj_penultimate hnon
  have hsz : z ≠ p.snd := hs.ne
  have htz : p.penultimate ≠ z := ht.ne
  apply hp.snd_ne_penultimate
  apply Subtype.ext
  have hz := z.property
  have hsmem := p.snd.property
  have htmem := p.penultimate.property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hsmem htmem
  grind

lemma path_toSubgraph_spanningCoe_isAcyclic {G : SimpleGraph α} {u v : α}
    {p : G.Walk u v} (hp : p.IsPath) : p.toSubgraph.spanningCoe.IsAcyclic := by
  induction p with
  | nil => simp [Walk.toSubgraph]
  | @cons u v w huv p ih =>
      rw [Walk.cons_isPath_iff] at hp
      have ihA := ih hp.1
      have hu_not : u ∉ p.toSubgraph.verts := by
        simpa [Walk.mem_verts_toSubgraph] using hp.2
      have hNbr : p.toSubgraph.spanningCoe.neighborSet u = ∅ := by
        ext x
        constructor
        · intro hx
          have hu_mem : u ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hx
          exact (hu_not hu_mem).elim
        · simp
      have hnreach : ¬p.toSubgraph.spanningCoe.Reachable u v :=
        not_reachable_of_neighborSet_left_eq_empty huv.ne hNbr
      have hadd :=
        (isAcyclic_add_edge_iff_of_not_reachable u v hnreach).2 ihA
      simpa [Walk.toSubgraph, sup_comm] using hadd

lemma path_toSubgraph_isTree {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath) : p.toSubgraph.coe.IsTree := by
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  exact IsAcyclic.embedding p.toSubgraph.coeEmbeddingSpanningCoe
    (path_toSubgraph_spanningCoe_isAcyclic hp)

lemma two_le_largestInducedTreeSize (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) [Nontrivial α] :
    2 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne α
  obtain ⟨w, huw⟩ : ∃ w, G.Adj u w := by
    obtain ⟨p⟩ := hG u v
    cases p with
    | nil => exact (huv rfl).elim
    | cons h p => exact ⟨_, h⟩
  unfold largestInducedTreeSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨s, rfl, _⟩
      exact s.card_le_univ⟩
  · refine ⟨{u, w}, by simp [huw.ne], ?_⟩
    have hset : (↑({u, w} : Finset α) : Set α) = ({u, w} : Set α) := by
      ext x
      simp
    rw [hset]
    exact induce_pair_isTree_of_adj huw

lemma conjecture143_of_girth_zero [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hσ : 0 < secondSmallestDegree G) (hg : G.girth = 0) :
    (G.girth : ℝ) + 1 ≤
      (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  have ht : 0 < largestInducedTreeSize G :=
    lt_of_lt_of_le (by norm_num) (two_le_largestInducedTreeSize G hG)
  have hprod : 0 < largestInducedTreeSize G * secondSmallestDegree G :=
    Nat.mul_pos ht hσ
  have hone : 1 ≤ largestInducedTreeSize G * secondSmallestDegree G := hprod
  rw [hg]
  norm_num
  exact_mod_cast hone

lemma conjecture143_of_large_sigma (G : SimpleGraph α) [DecidableRel G.Adj]
    (hgirth : 3 ≤ G.girth)
    (htree : G.girth - 1 ≤ largestInducedTreeSize G)
    (hσ : 2 ≤ secondSmallestDegree G) :
    (G.girth : ℝ) + 1 ≤
      (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  have htreeNat : G.girth ≤ largestInducedTreeSize G + 1 := by omega
  have htreeR : (G.girth : ℝ) ≤ (largestInducedTreeSize G : ℝ) + 1 := by
    exact_mod_cast htreeNat
  have hσR : (2 : ℝ) ≤ secondSmallestDegree G := by
    exact_mod_cast hσ
  have hgirthR : (3 : ℝ) ≤ G.girth := by
    exact_mod_cast hgirth
  have htreeNonneg : (0 : ℝ) ≤ largestInducedTreeSize G := by positivity
  have hmul :
      2 * (largestInducedTreeSize G : ℝ) ≤
        (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hσR htreeNonneg]
  nlinarith

end WrittenOnTheWallII.GraphConjecture143
