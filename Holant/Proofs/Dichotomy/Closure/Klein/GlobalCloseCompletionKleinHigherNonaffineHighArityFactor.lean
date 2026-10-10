import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFiberVariation
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFiberTheorem

/-! Source high-arity Pauli factor proposition. One literal cross contraction
leaves the protected pair and two untouched permutation-labeled edges, giving
three varying coordinates in a four-term safe card, contrary to full8.4. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant.Certificates.MatchingContractionClosure
open MatchingCard
namespace Fiber
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

theorem high_arity_permutation_obstruction (M : Matching P r) (hr : 5 ≤ r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (hfirst : ∀ a, labels a ⟨0,by omega⟩ = a)
    (hw : ∀ a, weight a ≠ 0) (hbij : ∀ e, Function.Bijective (fun a => labels a e)) :
    ¬ PairSafe (tensor M weight labels) := by
  intro hs
  let ix : Fin 5 → Fin r := Fin.castLE hr
  have hinj : Function.Injective ix := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun i : Fin r => i.val) hab
  let e := ix 1
  let f := ix 2
  have hef : e ≠ f := fun h => (by decide : (1 : Fin 5) ≠ 2) (hinj h)
  let j (a : Fin 5) (ha : a ≠ 2) := (Fintype.equivFin (OtherEdges f)) ⟨ix a,fun h => ha (hinj h)⟩
  let j0 := j 0 (by decide)
  let j3 := j 3 (by decide)
  let j4 := j 4 (by decide)
  have hjinj (a b : Fin 5) (ha : a ≠ 2) (hb : b ≠ 2) (heq : j a ha = j b hb) : a = b := by
    apply hinj
    exact congrArg Subtype.val ((Fintype.equivFin (OtherEdges f)).injective heq)
  have hjlabel (a : Label) (i : Fin 5) (hi : i ≠ 1) (hi' : i ≠ 2) :
      fusedLabels e f 0 labels a (j i hi') = labels a (ix i) := by
    have hne : ix i ≠ e := fun h => hi (hinj h)
    simp only [fusedLabels,j,Equiv.symm_apply_apply,hne,ite_false]
  have hlabel (a : Label) : fusedLabels e f 0 labels a j0 = a := by
    rw [hjlabel a 0 (by decide) (by decide)]
    exact hfirst a
  have varies (i : Fin 5) (hi : i ≠ 1) (hi' : i ≠ 2) :
      LabelVaries (fusedLabels e f 0 labels) (j i hi') := by
    obtain ⟨a,ha⟩ := (hbij (ix i)).2 0
    obtain ⟨b,hb⟩ := (hbij (ix i)).2 xLabel
    dsimp only at ha hb
    refine ⟨a,b,?_⟩
    rw [hjlabel a i hi hi',hjlabel b i hi hi',ha,hb]
    exact zero_ne_x
  have h03 : j0 ≠ j3 := fun h => (by decide : (0 : Fin 5) ≠ 3) (hjinj _ _ _ _ h)
  have h04 : j0 ≠ j4 := fun h => (by decide : (0 : Fin 5) ≠ 4) (hjinj _ _ _ _ h)
  have h34 : j3 ≠ j4 := fun h => (by decide : (3 : Fin 5) ≠ 4) (hjinj _ _ _ _ h)
  have hwn (a : Label) : fusedWeight weight labels e f 0 a ≠ 0 :=
    fun h => hw a ((fusedWeight_zero_iff weight labels e f 0 a).mp h)
  have hnot := three_variable_edges_not_safe (fusedMatching M e f) (fusedWeight weight labels e f 0)
    (fusedLabels e f 0 labels) j0 hlabel hwn j0 j3 j4 h03 h04 h34
    (varies 0 (by decide) (by decide)) (varies 3 (by decide) (by decide)) (varies 4 (by decide) (by decide))
  apply hnot
  have huv : M.ports (e,true) ≠ M.ports (f,false) :=
    fun h => hef (congrArg Prod.fst (M.ports.injective h))
  have hh := hs _ _ huv 0
  rwa [contract_cross_fiber M weight labels e f hef 0] at hh

end Fiber

namespace MatchingCard

/-- Every even arity at least ten is covered by r≥2 and arity 2*r+6.
Only actual original pair safety is assumed; all normal-form and permutation
facts are derived from the tensor and the negated genuine factor predicate. -/
theorem high_arity_factor_of_pairSafe (r : ℕ) (hr : 2 ≤ r) (f : Signature ℂ (2*r+6))
    (hf : f ≠ 0) (hs : PairSafe f) : Fiber.HasProperTensorFactor f := by
  by_contra hp
  obtain ⟨s,M,weight,labels,hfirst,he,hzero,hsize⟩ :=
    common_full_fiber r (by omega) f hf ((pairSafe_iff_ordered f).mp hs)
  have hcard := M.port_card
  simp only [Fintype.card_fin] at hcard
  have hsafe : PairSafe (Fiber.tensor M weight labels) := by rwa [←he]
  have hn : Fiber.tensor M weight labels ≠ 0 := by rwa [←he]
  have hp' : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels) := by rwa [←he]
  obtain ⟨hw,hbij⟩ := Fiber.dichotomy M (by omega) weight labels 0 hfirst hsafe hn hp'
  exact Fiber.high_arity_permutation_obstruction M (by omega) weight labels hfirst hw hbij hsafe

/-- The manuscript's literal arity convention: f has arity 2*r≥10. -/
theorem high_arity_factor (r : ℕ) (hr : 5 ≤ r) (f : Signature ℂ (2*r))
    (hf : f ≠ 0) (hs : PairSafe f) : Fiber.HasProperTensorFactor f := by
  let e : Fin (2*r) ≃ Fin (2*(r-3)+6) := finCongr (by omega)
  have hn : Tensor.reindex e f ≠ 0 := by
    intro hz
    have he := congrArg (Tensor.reindex e.symm) hz
    rw [Tensor.reindex_symm] at he
    exact hf he
  have hp := high_arity_factor_of_pairSafe (r-3) (by omega) (Tensor.reindex e f) hn
    (pairSafe_reindex e f hs)
  exact (Fiber.factor_reindex_iff e f).mp hp

end MatchingCard
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
