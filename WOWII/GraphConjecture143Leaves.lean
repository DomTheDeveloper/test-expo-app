import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma degree_pos_of_connected [Nontrivial α] {G : SimpleGraph α}
    (hG : G.Connected) (v : α) : 0 < G.degree v := by
  obtain ⟨u, huv⟩ : ∃ u, G.Adj v u := by
    obtain ⟨w, hvw⟩ := exists_pair_ne α
    obtain ⟨p⟩ := hG v w
    cases p with
    | nil => exact (hvw rfl).elim
    | cons h p => exact ⟨_, h⟩
  exact Finset.card_pos.mpr ⟨u, by simpa using huv⟩

/-- If a connected nontrivial graph has second-smallest degree one, then it has
at least two distinct degree-one vertices. -/
lemma exists_two_degree_one_of_secondSmallestDegree_eq_one [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hσ : secondSmallestDegree G = 1) :
    ∃ x y : α, x ≠ y ∧ G.degree x = 1 ∧ G.degree y = 1 := by
  let ds := degreeSequence G
  have hlen : ds.length = Fintype.card α := by
    simp [ds, degreeSequence]
  have hcard : 2 ≤ Fintype.card α := Fintype.two_le_card
  have h1lt : 1 < ds.length := by omega
  have hget1 : ds[1] = 1 := by
    rw [← List.getD_eq_getElem ds 0 h1lt]
    simpa [ds, secondSmallestDegree] using hσ
  have hsorted : ds.Pairwise (· ≤ ·) := by
    simp [ds, degreeSequence]
  have hget0le : ds[0] ≤ ds[1] := by
    exact hsorted.rel_get_of_lt (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (by omega)
  have hget0pos : 0 < ds[0] := by
    have hm : ds[0] ∈ ds := List.getElem_mem
    have hm' : ds[0] ∈ Finset.univ.val.map (fun v => G.degree v) := by
      simpa [ds, degreeSequence] using hm
    obtain ⟨v, -, hv⟩ := Multiset.mem_map.mp hm'
    rw [← hv]
    exact degree_pos_of_connected hG v
  have hget0 : ds[0] = 1 := by omega
  have hcount_ds : 2 ≤ ds.count 1 := by
    have h0 : ds.getD 0 0 = 1 := by
      rw [List.getD_eq_getElem ds 0 (by omega)]
      exact hget0
    have h1 : ds.getD 1 0 = 1 := by
      rw [List.getD_eq_getElem ds 0 h1lt]
      exact hget1
    rcases ds with _ | d0 (_ | d1 tail)
    · simp at hlen
    · simp at hlen
    · simp_all
  have hcount_orig :
      2 ≤ (Finset.univ.val.map (fun v => G.degree v)).count 1 := by
    simpa [ds, degreeSequence] using hcount_ds
  have hcount_vertices :
      2 ≤ Finset.univ.val.countP (fun v => G.degree v = 1) := by
    simpa [Multiset.count, Function.comp_def, eq_comm] using hcount_orig
  let L : Finset α := Finset.univ.filter (fun v => G.degree v = 1)
  have hLcard : 2 ≤ L.card := by
    simpa [L, Multiset.card_filter] using hcount_vertices
  have hLnonempty : L.Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) hLcard)
  obtain ⟨x, hx⟩ := hLnonempty
  have herase : 0 < (L.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp herase
  have hyL : y ∈ L := Finset.mem_of_mem_erase hy
  have hyx : y ≠ x := Finset.ne_of_mem_erase hy
  refine ⟨x, y, hyx.symm, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hx).2
  · exact (Finset.mem_filter.mp hyL).2

end WrittenOnTheWallII.GraphConjecture143
