import Holant.Platonic.RainbowLocalization.RetainedLabels

/-! The indexed finite-family input imposes no new source restriction. Any
finite retained set admits exactly this representation, including the empty set. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant

 theorem finite_family_enumeration {K : Type*} [Zero K]
    (F : SignatureFamily K) (hF : F.Finite) :
    ∃ (s : ℕ) (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature K (arity i.val)),
      indexedRetainedFamily arity signatures=F := by
  classical
  letI := hF.fintype
  let s := Fintype.card F
  let e : Fin s ≃ F := (Fintype.equivFin F).symm
  let item : ℕ → AnySignature K := fun i =>
    if hi : i<s then (e ⟨i,hi⟩).val else ⟨0,0⟩
  let arity : ℕ → ℕ := fun i => (item i).1
  let signatures : (i : Fin s) → Signature K (arity i.val) := fun i => (item i.val).2
  refine ⟨s,arity,signatures,?_⟩
  change Set.range (fun i : Fin s => item i.val)=F
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    simpa only [item,dif_pos i.isLt] using (e i).property
  · intro hf
    refine ⟨e.symm ⟨f,hf⟩,?_⟩
    simp only [item,dif_pos (e.symm ⟨f,hf⟩).isLt,e.apply_symm_apply]

 theorem finite_algebraic_family_enumeration (F : SignatureFamily ℂ) (hF : F.Finite)
    (halg : ∀f ∈ F,∀x,IsAlgebraic ℚ (f.2 x)) :
    ∃ (s : ℕ) (arity : ℕ → ℕ) (signatures : (i : Fin s) → Signature ℂ (arity i.val)),
      indexedRetainedFamily arity signatures=F ∧ ∀i x,IsAlgebraic ℚ (signatures i x) := by
  obtain ⟨s,arity,signatures,he⟩ := finite_family_enumeration F hF
  refine ⟨s,arity,signatures,he,?_⟩
  intro i x
  apply halg ⟨arity i.val,signatures i⟩ _ x
  rw [←he]
  exact ⟨i,rfl⟩

end Holant.Platonic.RainbowLocalization.Physical
