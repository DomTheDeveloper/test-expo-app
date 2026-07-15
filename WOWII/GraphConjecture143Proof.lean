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
  | nil =>
      change (⊥ : SimpleGraph α).IsAcyclic
      exact isAcyclic_bot
  | @cons u v w huv p ih =>
      rw [Walk.cons_isPath_iff] at hp
      have ihA := ih hp.1
      have hu_not : u ∉ p.toSubgraph.verts := by
        simpa [Walk.mem_verts_toSubgraph] using hp.2
      have hnreach : ¬p.toSubgraph.spanningCoe.Reachable u v := by
        rintro ⟨q⟩
        have hq : ¬q.Nil := Walk.not_nil_of_ne huv.ne
        have hadj := q.adj_snd hq
        exact hu_not (p.toSubgraph.edge_vert hadj)
      have hadd :=
        (isAcyclic_add_edge_iff_of_not_reachable u v hnreach).2 ihA
      simpa [Walk.toSubgraph, sup_comm] using hadd

lemma path_toSubgraph_isTree {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath) : p.toSubgraph.coe.IsTree := by
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  let f : p.toSubgraph.coe ↪g p.toSubgraph.spanningCoe where
    toFun := Subtype.val
    inj' := Subtype.val_injective
    map_rel_iff' := Iff.rfl
  exact IsAcyclic.embedding f (path_toSubgraph_spanningCoe_isAcyclic hp)

lemma edge_getVert_succ_mem_edges {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    {i : ℕ} (hi : i < p.length) : s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
  have hd : p.darts[i] ∈ p.darts := List.getElem_mem _
  have hm : (p.darts[i]).edge ∈ p.edges := by
    exact List.mem_map_of_mem _ hd
  rw [p.darts_getElem_eq_getVert i (by simpa [p.length_darts] using hi)] at hm
  exact hm

lemma geodesic_adj_mem_edges {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hgeo : p.length = G.dist u v) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) :
    s(p.getVert i, p.getVert j) ∈ p.edges := by
  have hne : i ≠ j := by
    intro hij
    subst j
    exact hadj.ne rfl
  have forward : ∀ {a b : ℕ}, a < b → b ≤ p.length →
      G.Adj (p.getVert a) (p.getVert b) →
      s(p.getVert a, p.getVert b) ∈ p.edges := by
    intro a b hab hb habadj
    let q := (p.drop a).take (b - a)
    have hqsub : q.IsSubwalk p :=
      (Walk.isSubwalk_take (p.drop a) (b - a)).trans (Walk.isSubwalk_drop p a)
    have hseg := length_eq_dist_of_subwalk hgeo hqsub
    have hseg' : b - a = G.dist (p.getVert a) (p.getVert b) := by
      simpa [q, Nat.min_eq_left (by omega), Nat.add_sub_of_le hab.le] using hseg
    have hdiff : b - a = 1 := by
      rw [dist_eq_one_iff_adj.mpr habadj] at hseg'
      exact hseg'
    have hba : b = a + 1 := by omega
    subst b
    exact edge_getVert_succ_mem_edges p (by omega)
  by_cases hij : i < j
  · exact forward hij hj hadj
  · have hji : j < i := by omega
    simpa [Sym2.eq_swap] using forward hji hi hadj.symm

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
