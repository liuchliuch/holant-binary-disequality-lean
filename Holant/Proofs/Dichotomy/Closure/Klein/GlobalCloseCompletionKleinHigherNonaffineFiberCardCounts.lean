import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFiberSurgery

/-! Exact support counts for literal proper fiber cards. These are consequences
of the actual matching-overlap theorem, with no assumptions on cancellations. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Holant.Certificates.MatchingContractionClosure
open MatchingCard
namespace Fiber
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

theorem selectedWeight_live (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e : Fin r) (b a : Label) :
    selectedWeight weight labels e b a ≠ 0 ↔ weight a ≠ 0 ∧ labels a e = b := by
  by_cases h : labels a e = b <;> simp [selectedWeight,h]

theorem edge_fiber_count (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished e : Fin r) (hde : distinguished ≠ e) (hlabel : ∀ a, labels a distinguished = a)
    (hs : PairSafe (tensor M weight labels)) (b : Label) :
    Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} = 0 ∨
    Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} = 1 ∨
    Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} = 4 := by
  classical
  let j := (Fintype.equivFin (OtherEdges e)) ⟨distinguished,hde⟩
  have hj (a : Label) : deletedLabels e labels a j = a := by
    simp only [deletedLabels,j,Equiv.symm_apply_apply,hlabel]
  have huv : M.ports (e,false) ≠ M.ports (e,true) := by
    intro h
    have hh := congrArg Prod.snd (M.ports.injective h)
    cases hh
  have hh := hs _ _ huv b
  rw [contract_edge M weight labels e b] at hh
  have hc := safe_support_card (deletedMatching M e) (selectedWeight weight labels e b)
    (deletedLabels e labels) j hj hh
  have he : Fintype.card {a : Label // selectedWeight weight labels e b a ≠ 0} =
      Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun a => selectedWeight_live weight labels e b a))
  rwa [he] at hc

theorem cross_live_count (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished e f : Fin r) (hde : distinguished ≠ e) (hdf : distinguished ≠ f) (hef : e ≠ f)
    (hlabel : ∀ a, labels a distinguished = a) (hs : PairSafe (tensor M weight labels)) :
    Fintype.card {a : Label // weight a ≠ 0} = 0 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 1 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 4 := by
  classical
  let j := (Fintype.equivFin (OtherEdges f)) ⟨distinguished,hdf⟩
  have hj (a : Label) : fusedLabels e f 0 labels a j = a := by
    simp only [fusedLabels,j,Equiv.symm_apply_apply,hde,ite_false,hlabel]
  have huv : M.ports (e,true) ≠ M.ports (f,false) := by
    intro h
    exact hef (congrArg Prod.fst (M.ports.injective h))
  have hh := hs _ _ huv 0
  rw [contract_cross_fiber M weight labels e f hef 0] at hh
  have hc := safe_support_card (fusedMatching M e f) (fusedWeight weight labels e f 0)
    (fusedLabels e f 0 labels) j hj hh
  have he : Fintype.card {a : Label // fusedWeight weight labels e f 0 a ≠ 0} =
      Fintype.card {a : Label // weight a ≠ 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun a => not_congr (fusedWeight_zero_iff weight labels e f 0 a)))
  rwa [he] at hc

theorem two_other_edges (hr : 3 ≤ r) (d : Fin r) :
    ∃ e f : Fin r, d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨e,hed⟩ := exists_ne d
  have hex : ∃ f : Fin r, f ≠ d ∧ f ≠ e := by
    by_contra hn
    push_neg at hn
    have hsub : (Finset.univ : Finset (Fin r)) ⊆ {d,e} := by
      intro f hf
      by_cases hd : f = d
      · simp [hd]
      · simp [hn f hd]
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    have hp : ({d,e} : Finset (Fin r)).card = 2 := by simp [hed.symm]
    omega
  obtain ⟨f,hfd,hfe⟩ := hex
  exact ⟨e,f,hed.symm,hfd.symm,hfe.symm⟩

theorem proper_card_live_count (M : Matching P r) (hr : 3 ≤ r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished : Fin r)
    (hlabel : ∀ a, labels a distinguished = a) (hs : PairSafe (tensor M weight labels)) :
    Fintype.card {a : Label // weight a ≠ 0} = 0 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 1 ∨
    Fintype.card {a : Label // weight a ≠ 0} = 4 := by
  obtain ⟨e,f,hde,hdf,hef⟩ := two_other_edges hr distinguished
  exact cross_live_count M weight labels distinguished e f hde hdf hef hlabel hs

end Fiber
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
