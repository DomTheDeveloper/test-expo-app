import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
Short-cycle lemmas for the proof of WOWII Graph Conjecture 143.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A path with fewer vertices than the girth cannot acquire a cycle when all
edges induced by its support are added. -/
lemma short_path_support_induces_tree {G : SimpleGraph α} {u v : α}
    {p : G.Walk u v} (hp : p.IsPath) (hshort : p.length + 1 < G.girth) :
    (G.induce {x : α | x ∈ p.support}).IsTree := by
  let S : Set α := {x : α | x ∈ p.support}
  have hconn : (G.induce S).Connected := by
    let f : p.toSubgraph.coe →g G.induce S :=
      ⟨fun x => ⟨x.1, by simpa [S, Walk.mem_verts_toSubgraph] using x.2⟩,
        fun h => by simpa using p.toSubgraph.adj_sub h⟩
    apply p.toSubgraph_connected.coe.map f
    intro x
    refine ⟨⟨x.1, ?_⟩, Subtype.ext rfl⟩
    simp [S, x.2]
  refine ⟨hconn, ?_⟩
  intro z c hc
  let incl : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  have hcG : (c.map incl).IsCycle := hc.map Subtype.val_injective
  have hg : G.girth ≤ c.length := by
    simpa using G.girth_le_length hcG
  have hcard : c.length ≤ Fintype.card S := by
    simpa [S, Walk.length_support] using hc.support_nodup.length_le_card
  have hScard : Fintype.card S = p.length + 1 := by
    rw [← Set.toFinset_card]
    have hfin : S.toFinset = p.support.toFinset := by
      ext x
      simp [S]
    rw [hfin, List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  omega

/-- Deleting two consecutive edges from a shortest cycle leaves an induced tree
on `girth G - 1` vertices. -/
lemma girth_sub_one_le_largestInducedTreeSize (G : SimpleGraph α)
    [DecidableRel G.Adj] (hcyc : ¬G.IsAcyclic) :
    G.girth - 1 ≤ largestInducedTreeSize G := by
  obtain ⟨a, w, hw, hgw⟩ := SimpleGraph.exists_girth_eq_length.mpr hcyc
  cases w with
  | nil => exact (hw.not_nil rfl).elim
  | @cons a b h p =>
      have hp : p.IsPath := ((Walk.cons_isCycle_iff p h).mp hw).1
      let q := p.tail
      have hq : q.IsPath := hp.tail
      have hgw' : G.girth = p.length + 1 := by
        simpa [Walk.length_cons] using hgw
      have hplen : 2 ≤ p.length := by
        have hthree := hw.three_le_length
        simp only [Walk.length_cons] at hthree
        omega
      have hqlen : q.length + 1 = G.girth - 1 := by
        simp only [q, Walk.tail, Walk.drop_length]
        omega
      have hshort : q.length + 1 < G.girth := by omega
      have htree := short_path_support_induces_tree hq hshort
      unfold largestInducedTreeSize
      apply le_csSup
      · exact ⟨Fintype.card α, by
          rintro n ⟨s, rfl, _⟩
          exact s.card_le_univ⟩
      · refine ⟨q.support.toFinset, ?_, ?_⟩
        · rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support, hqlen]
        · have hset : (↑q.support.toFinset : Set α) = {x : α | x ∈ q.support} := by
            ext x
            simp
          rw [hset]
          exact htree

end WrittenOnTheWallII.GraphConjecture143
