import Holant.Platonic.StabilizerShortening.CorrectableForms
import Holant.Platonic.StabilizerShortening.PortExtension
import Holant.Platonic.StabilizerShortening.CliffordAffine

/-! The correctable-erasure branch of source Lemma 9.21. A pure port is
an actual positive-arity tensor factor. A mixed port and one untouched
auxiliary port give the literal Q0 card, with its exact positive scalar. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.TetrahedralAffine
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k n m : ℕ}

def bellPorts (r : Fin (n+1)) : (Bool ⊕ Fin n) ≃ Fin ((n+1)+1) where
  toFun := Sum.elim (fun b=>if b then r.succ else 0) (fun j=>(r.succAbove j).succ)
  invFun := Fin.cases (.inl false) (fun j=>if h : j=r then .inl true else
    .inr ((finSuccAboveEquiv r).symm ⟨j,h⟩))
  left_inv j := by
    cases j with
    | inl b => cases b <;> simp
    | inr j => simp [Fin.succAbove_ne,←finSuccAboveEquiv_apply]
  right_inv j := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [Fin.cases_succ]
      split_ifs with h
      · subst j;simp
      · exact congrArg Fin.succ
          (congrArg Subtype.val ((finSuccAboveEquiv r).apply_symm_apply ⟨j,h⟩))

theorem pairInsert_bellPorts (r : Fin (n+1)) (a b : Bool) (x : Word n) :
    pairInsert (bellPorts r) a b x=Fin.cons a (r.insertNth b x) := by
  ext j
  obtain ⟨j,rfl⟩ := (bellPorts r).surjective j
  cases j with
  | inl c =>
    cases c <;> simp only [pairInsert_first,pairInsert_second] <;> simp [bellPorts]
  | inr j => rw [pairInsert_remaining];simp [bellPorts]

theorem auxiliaryKet_columns (f : Signature ℂ (k+1)) :
    auxiliaryKet false (column 0 false f)+auxiliaryKet true (column 0 true f)=f := by
  apply columns_ext
  intro b
  cases b <;> simp

/-- Equality is literally the Q0 representative in the contraction-kernel
convention, and the card is exactly the mixed residual scaled by 1/√2. -/
theorem mixed_bell_card (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (r : Fin (n+1)) (W : Signature ℂ (k+1) →ₗ[ℂ] Signature ℂ n)
    (he : ∀f b w,U f (r.insertNth b w)=(sqrtTwo : ℂ)⁻¹*W (auxiliaryKet b f) w) :
    (pairCard (bellPorts r) (complexKernel (.inl 0))).comp (prependMap U)=
      (sqrtTwo : ℂ)⁻¹ • W := by
  apply LinearMap.ext
  intro f
  ext w
  change (∑a : Bool,∑b : Bool,complexKernel (.inl 0) a b*
    prependMap U f (pairInsert (bellPorts r) a b w))=(sqrtTwo : ℂ)⁻¹*W f w
  simp only [pairInsert_bellPorts]
  simp only [complexKernel,quaternionBasis,Matrix.cons_val_zero,Q0,Signature.equality,
    Fintype.sum_bool,prependMap,LinearMap.coe_mk,AddHom.coe_mk,Fin.cons_zero,Fin.tail_cons,
    Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,zero_mul,one_mul,zero_add,add_zero]
  rw [he,he]
  rw [←mul_add]
  have ha := congrFun (map_add W (auxiliaryKet true (column 0 true f))
    (auxiliaryKet false (column 0 false f))) w
  simp only [Pi.add_apply] at ha
  rw [←ha,add_comm (auxiliaryKet true (column 0 true f)),auxiliaryKet_columns]

theorem prependMap_smul (c : ℂ) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    prependMap (c • U)=c • prependMap U := by
  apply LinearMap.ext
  intro f
  ext w
  rfl

/-- Keep the Bell pair fixed while arbitrarily many further physical ports
are left untouched. The residual map remains a source-semantic isometry. -/
theorem mixed_extended_card (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (r : Fin (n+1)) (h : MixedStabilizerForm U r) (t : ℕ) :
    ∃W : Signature ℂ (k+(t+1)) →ₗ[ℂ] Signature ℂ (n+t),
      IsStabilizerIsometry W ∧
      ∃p : (Bool ⊕ Fin (n+t)) ≃ Fin ((n+1)+(t+1)),
        (pairCard p (complexKernel (.inl 0))).comp (tensorMap (t+1) U)=
          (sqrtTwo : ℂ)⁻¹ • W := by
  induction t with
  | zero =>
    obtain ⟨W,hW,he⟩ := h
    exact ⟨W,hW,bellPorts r,mixed_bell_card U r W he⟩
  | succ t ih =>
    obtain ⟨W,hW,p,hp⟩ := ih
    refine ⟨prependMap W,prependMap_stabilizer W hW,prependSplitPorts p,?_⟩
    rw [pairCard_prepend,tensorMap_succ,←prependMap_comp,hp,prependMap_smul]

theorem pure_correctable_factor (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (hU : IsStabilizerIsometry U) (r : Fin (n+1)) (h : PureAxisForm U r)
    (t : ℕ) (ht : 1≤t) (xi : Signature ℂ (k+t)) (hxi : ¬ComplexAffine xi) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (tensorMap t U xi) := by
  obtain ⟨u,W,hW,he⟩ := pureAxisForm_separation U r h
  have hu : U=unaryFactorMap (unaryPorts r) (fun x=>u (x 0)) W := by
    apply LinearMap.ext
    intro f
    ext w
    exact he f w
  have hx : xi≠0 := by intro hz;exact hxi (hz ▸ affine_zero_complex)
  have hf : tensorMap t U xi≠0 := by
    intro hz
    exact hx ((isometry_injective _ (tensorMap_stabilizer t U hU).1) (by simpa using hz))
  rw [hu,unaryFactorMap_tensorMap] at hf ⊢
  exact unaryFactorMap_proper _ _ _ xi (by omega) hf

theorem mixed_correctable_card (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (r : Fin (n+1)) (h : MixedStabilizerForm U r)
    (t : ℕ) (ht : 1≤t) (xi : Signature ℂ (k+t)) (hxi : ¬ComplexAffine xi) :
    HasNonaffineTetrahedralCard (tensorMap t U xi) := by
  cases t with
  | zero => omega
  | succ t =>
    obtain ⟨W,hW,p,hp⟩ := mixed_extended_card U r h t
    have hn : ¬ComplexAffine ((pairCard p (complexKernel (.inl 0))) (tensorMap (t+1) U xi)) := by
      intro hg
      have he := congrArg (fun L : Signature ℂ (k+(t+1)) →ₗ[ℂ] Signature ℂ (n+t)=>L xi) hp
      rw [LinearMap.comp_apply] at he
      rw [he] at hg
      have hs : (sqrtTwo : ℂ)⁻¹≠0 := inv_ne_zero (by exact_mod_cast sqrtTwo_ne_zero)
      exact hxi ((semantic_isometry_affine_iff W hW xi).mp
        ((affine_complex_scale_iff _ hs (W xi)).mp hg))
    exact ⟨n+t,p,.inl 0,fun hz=>hn (hz ▸ affine_zero_complex),hn⟩

/-- Correctable-erasure branch of source Lemma 9.21, with a genuine proper
tensor factor or a nonzero nonaffine literal tetrahedral card. -/
theorem correctable_shortening
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (hU : IsStabilizerIsometry U)
    (t : ℕ) (ht : 1≤t) (xi : Signature ℂ (k+t)) (hxi : ¬ComplexAffine xi)
    (h : ∃r,CorrectableMap U r) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (tensorMap t U xi) ∨
      HasNonaffineTetrahedralCard (tensorMap t U xi) := by
  obtain ⟨r,hr⟩ := h
  rcases semantic_correctable_axis_or_mixed U hU r hr with hp|hm
  · exact Or.inl (pure_correctable_factor U hU r hp t ht xi hxi)
  · exact Or.inr (mixed_correctable_card U r hm t ht xi hxi)

end
end Holant.Platonic.StabilizerShortening
