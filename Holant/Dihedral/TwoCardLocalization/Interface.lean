import Holant.Dihedral.TwoCardLocalization.ActualCards

/-! Source Lemma6.6: one actual six-port ancestor, its two selected inherited
actual cards, exact original-pair retention, a linear representative count,
and the proved exclusion of every three-factor current-group product. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
set_option backward.isDefEq.respectTransparency false

theorem Disagreement.scale_pair {m n : ℕ} {q₀ q₁ : Signature Scalar n}
    (h : Disagreement m n q₀ q₁) (c₀ c₁ : Scalar) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) :
    Disagreement m n (c₀ • q₀) (c₁ • q₁) := by
  rcases h with h|h
  · left
    obtain ⟨M₀,M₁,h₀,h₁,hs₀,hs₁,rfl,rfl,hd⟩ := h
    refine ⟨{M₀ with scalar := c₀*M₀.scalar},{M₁ with scalar := c₁*M₁.scalar},h₀,h₁,
      mul_ne_zero hc₀ hs₀,mul_ne_zero hc₁ hs₁,?_,?_,hd⟩
    all_goals funext x; simp [MatchingContractionClosure.Presentation.tensor,
      MatchingContractionClosure.productValue,Pi.smul_apply,smul_eq_mul,mul_assoc]
  · right
    obtain ⟨s,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,rfl,rfl,he⟩ := h
    refine ⟨s,p,A₀,A₁,c₀*κ₀,c₁*κ₁,hA₀,hA₁,mul_ne_zero hc₀ hκ₀,mul_ne_zero hc₁ hκ₁,?_,?_,he⟩
    all_goals funext x; simp [MatchingContractionClosure.productValue,Pi.smul_apply,smul_eq_mul,mul_assoc]

structure LocalizationResult {m r : ℕ} (F : SignatureFamily Scalar)
    (labels : Bool → PhaseLabel m) (f : Signature Scalar (2*r+6)) where
  program : Program (PhaseLabel m) (2*r+4) 4
  scalar : Scalar
  scalar_ne_zero : scalar ≠ 0
  representative_count : program.length=r
  actual : Gadget.Realizes F .disequality (scalar • program.core phaseKernel f)
  inherited : ∀ b,Signature.contract (phaseKernel (labels b)) (scalar • program.core phaseKernel f)=
    scalar • program.residual phaseKernel (Signature.contract (phaseKernel (labels b)) f)
  disagreement : Disagreement m 4
    (Signature.contract (phaseKernel (labels false)) (scalar • program.core phaseKernel f))
    (Signature.contract (phaseKernel (labels true)) (scalar • program.core phaseKernel f))
  nonzero : ∀ b,Signature.contract (phaseKernel (labels b)) (scalar • program.core phaseKernel f) ≠ 0
  not_three_factor : ¬ ThreeFactor m (scalar • program.core phaseKernel f)
  cardScalar : Bool → Scalar
  cardScalar_ne_zero : ∀ b,cardScalar b ≠ 0
  actual_cards : ∀ b,Gadget.Realizes F .disequality
    (cardScalar b • Signature.contract (phaseKernel (labels b)) (scalar • program.core phaseKernel f))
  actual_disagreement : Disagreement m 4
    (cardScalar false • Signature.contract (phaseKernel (labels false)) (scalar • program.core phaseKernel f))
    (cardScalar true • Signature.contract (phaseKernel (labels true)) (scalar • program.core phaseKernel f))

/-- The exact linear bound concerns actual fixed representative uses in the
one-copy ancestor program, not an arithmetic or protocol cost annotation. -/
theorem LocalizationResult.exact_count {m r : ℕ} {F : SignatureFamily Scalar}
    {labels : Bool → PhaseLabel m} {f : Signature Scalar (2*r+6)} (R : LocalizationResult F labels f) :
    2*r+6=6+2*R.program.length := by rw [R.representative_count]; omega

/-- Full exact source statement. The only card assumptions are the two literal
actual original product presentations and their source-defined disagreement. -/
theorem source_two_card_localization {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (r : ℕ) (f : Signature Scalar (2*r+6)) (hf : Gadget.Realizes F .disequality f)
    (labels : Bool → PhaseLabel m)
    (D : PairProducts (G.connections (by omega)) labels f) (hd : D.Disagrees) :
    Nonempty (LocalizationResult F labels f) := by
  have h := D.disagreement (by omega : 0<m) hd
  obtain ⟨P,c,hc,hP,hactual,hout,hn₀,hn₁⟩ := actual_localization hm F G r f hf
    (phaseKernel (labels false)) (phaseKernel (labels true)) h
  let C := G.connections (by omega : 0<m)
  let q : Signature Scalar 6 := c • P.core phaseKernel f
  obtain ⟨a₀,ha₀,ha₀n,hd₀,hreal₀⟩ := actual_phase_connection F C q hactual (Equiv.refl _)
    (labels false).1 (labels false).2
  obtain ⟨a₁,ha₁,ha₁n,hd₁,hreal₁⟩ := actual_phase_connection F C q hactual (Equiv.refl _)
    (labels true).1 (labels true).2
  let d₀ := a₀*C.multiplier (labels false).1 (labels false).2
  let d₁ := a₁*C.multiplier (labels true).1 (labels true).2
  change Gadget.Realizes F .disequality (d₀ • Signature.contract (phaseKernel (labels false)) q) at hreal₀
  change Gadget.Realizes F .disequality (d₁ • Signature.contract (phaseKernel (labels true)) q) at hreal₁
  refine ⟨{
    program := P
    scalar := c
    scalar_ne_zero := hc
    representative_count := hP
    actual := hactual
    inherited := ?_
    disagreement := hout
    nonzero := ?_
    not_three_factor := ?_
    cardScalar := fun b => if b then d₁ else d₀
    cardScalar_ne_zero := ?_
    actual_cards := ?_
    actual_disagreement := ?_ }⟩
  · intro b
    rw [contract_smul,P.inherited_card]
  · intro b
    cases b
    · exact hn₀
    · exact hn₁
  · exact disagreement_not_three_factor (by omega) q _ _
      (M_mem_group (by omega) _ (labels false).2.property)
      (M_mem_group (by omega) _ (labels true).2.property) hout
  · intro b
    cases b
    · exact hd₀
    · exact hd₁
  · intro b
    cases b
    · exact hreal₀
    · exact hreal₁
  · exact hout.scale_pair d₀ d₁ hd₀ hd₁

/-- The same theorem for any specified original ordered deleted pair. The
permutation is an exact same-family boundary reindexing of the original core. -/
theorem source_two_card_localization_ordered {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (r : ℕ) (f : Signature Scalar (2*r+6)) (hf : Gadget.Realizes F .disequality f)
    (order : Equiv.Perm (Fin (2*r+6))) (labels : Bool → PhaseLabel m)
    (D : PairProducts (G.connections (by omega)) labels (Tensor.reindex order.symm f)) (hd : D.Disagrees) :
    Nonempty (LocalizationResult F labels (Tensor.reindex order.symm f)) :=
  source_two_card_localization hm F G r _ (realizes_reindex F .disequality f hf order) labels D hd

/-- The retained coordinate identities refer to the literal specified original
ordered endpoints, including their orientation. -/
theorem ordered_original_endpoints {n : ℕ} (order : Equiv.Perm (Fin (n+2)))
    (a b : Bool) (x : Fin n → Bool) :
    (fun i => CompatibleCoefficientLine.pair a b x (order.symm i)) (order 0)=a ∧
    (fun i => CompatibleCoefficientLine.pair a b x (order.symm i)) (order 1)=b := by
  simp only [Equiv.symm_apply_apply]
  exact ⟨rfl,rfl⟩

/-- Exact inherited-card formula in the original core's physical port order. -/
theorem LocalizationResult.ordered_inherited {m r : ℕ} {F : SignatureFamily Scalar}
    {labels : Bool → PhaseLabel m} {f : Signature Scalar (2*r+6)}
    (order : Equiv.Perm (Fin (2*r+6))) (R : LocalizationResult F labels (Tensor.reindex order.symm f))
    (b : Bool) :
    Signature.contract (phaseKernel (labels b))
      (R.scalar • R.program.core phaseKernel (Tensor.reindex order.symm f)) =
    R.scalar • R.program.residual phaseKernel (fun x => ∑ a : Bool,∑ c : Bool,
      phaseKernel (labels b) a c*f (fun i => CompatibleCoefficientLine.pair a c x (order.symm i))) :=
  R.inherited b

end Holant.Dihedral.TwoCardLocalization
