import Holant.Platonic.StabilizerErasure.EncoderRange
import Holant.Platonic.StabilizerErasure.NonzeroColumns
import Holant.Platonic.StabilizerCode.CommutingAlignmentPauli

/-! The source's primary, operator-level definition of a stabilizer isometry:
an actual isometry, an exact common eigenspace of commuting physical Paulis,
and physical representatives for every logical Pauli. A finite commuting
family generates a commuting Pauli subgroup with the same common +1 space.
All concrete Clifford encoders satisfy this definition by proved theorems.
-/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k m a : ℕ}

def HasStabilizerImage (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n) : Prop :=
  ∃t : ℕ,∃P : Fin t → Pauli n,
    (∀i j f,(P i).run ((P j).run f)=(P j).run ((P i).run f)) ∧
    ∀f,f∈LinearMap.range W ↔ ∀i,(P i).run f=f

def IsStabilizerIsometry (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n) : Prop :=
  (∀f g,hermitian (W f) (W g)=hermitian f g) ∧ HasStabilizerImage W ∧
    ∀Q : Pauli k,∃P : Pauli n,∀f,P.run (W f)=W (Q.run f)

theorem isometry_injective (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (h : ∀f g,hermitian (W f) (W g)=hermitian f g) : Function.Injective W := by
  intro f g he
  apply hermitian_ext
  intro v
  rw [←h v f,←h v g,he]

theorem one_signature_ne_zero : (fun _ : Word k => (1 : ℂ))≠0 := by
  intro h
  have he := congrFun h (origin k)
  norm_num at he

theorem pauli_one_ne_zero (Q : Pauli k) : Q.run (fun _ => 1)≠0 := by
  intro h
  have he := congrFun h (origin k)
  have hp : phaseRoot Q.phase=0 := by simpa [Pauli.run] using he
  exact phaseRoot_ne_zero Q.phase hp

theorem StabilizerIsometry.hasStabilizerImage (V : StabilizerIsometry k n) : HasStabilizerImage V.map := by
  let I := dualCode (coordinateCode V.coordinates)
  let e := Fintype.equivFin I
  have hp (z : I) : ∃P : Pauli n,∀f,
      P.run f=conjugatedZ (inverseClifford V.clifford) z.val f := by
    obtain ⟨c,a,b,he⟩ := conjugatedZ_is_standardPauli (inverseClifford V.clifford) z.val
    obtain ⟨P,hP⟩ := standardPauli_is_pauli c a b
    exact ⟨P,fun f => (hP f).trans (he f).symm⟩
  choose P hP using hp
  refine ⟨Fintype.card I,fun j => P (e.symm j),?_,?_⟩
  · intro i j f
    simp only [hP]
    exact conjugatedZ_commute _ _ _ _
  · intro f
    rw [V.mem_range_iff_pauli_fixed]
    constructor
    · intro hf j
      rw [hP]
      exact hf (e.symm j).val (e.symm j).property
    · intro hf z hz
      have he := hf (e ⟨z,hz⟩)
      simpa only [Equiv.symm_apply_apply,hP] using he

theorem StabilizerIsometry.semantic (V : StabilizerIsometry k n) : IsStabilizerIsometry V.map :=
  ⟨V.isometry,V.hasStabilizerImage,V.logical_representatives⟩

/-- Removing any actual fixed-zero tensor factor preserves both the exact
stabilizer code and every physical logical representative. This is a
derived closure theorem, not an assumed encoder for the residual map. -/
theorem remove_fixed_zero_stabilizer
    (V : Signature ℂ k →ₗ[ℂ] Signature ℂ m) (hV : IsStabilizerIsometry V)
    (e : BinaryVector m ≃ₗ[ZMod 2] BinaryVector n × BinaryVector a)
    (W : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hfactor : ∀f,V f=attachZero e (W f)) : IsStabilizerIsometry W := by
  obtain ⟨hiso,⟨t,P,hcomm,hcode⟩,hlogical⟩ := hV
  have hWiso (f g : Signature ℂ k) : hermitian (W f) (W g)=hermitian f g := by
    rw [←attachZero_isometry e,←hfactor,←hfactor,hiso]
  have hWi := isometry_injective W hWiso
  have hE : Function.Injective (attachZero e) := by
    intro f g he
    simpa using congrArg (evaluateZero e) he
  have hWone : W (fun _ => 1)≠0 := by
    intro hz
    exact one_signature_ne_zero (hWi (by simpa using hz))
  have hfixed (j : Fin t) (f : Signature ℂ k) : (P j).run (V f)=V f :=
    (hcode _).mp ⟨f,rfl⟩ j
  have hshift (j : Fin t) : (e (P j).shift).2=0 := by
    by_contra hj
    have he := congrArg (evaluateZero e) (hfixed j (fun _ => 1))
    rw [hfactor,evaluateZero_pauli_attachZero,if_neg hj,evaluateZero_attachZero] at he
    exact hWone he.symm
  have hinter (j : Fin t) (f : Signature ℂ n) :
      (P j).run (attachZero e f)=attachZero e ((logicalPauli e (P j)).run f) :=
    pauli_attachZero e (P j) (hshift j) f
  refine ⟨hWiso,⟨t,fun j => logicalPauli e (P j),?_,?_⟩,?_⟩
  · intro i j f
    apply hE
    rw [←hinter,←hinter,←hinter,←hinter,hcomm]
  · intro f
    constructor
    · rintro ⟨g,rfl⟩ j
      apply hE
      rw [←hinter,←hfactor,hfixed]
    · intro hf
      have hv : attachZero e f∈LinearMap.range V := by
        apply (hcode _).mpr
        intro j
        rw [hinter,hf]
      obtain ⟨g,hg⟩ := hv
      refine ⟨g,hE ?_⟩
      rw [←hfactor,hg]
  · intro Q
    obtain ⟨R,hR⟩ := hlogical Q
    have hs : (e R.shift).2=0 := by
      by_contra hs
      have he := congrArg (evaluateZero e) (hR (fun _ => 1))
      rw [hfactor,hfactor,evaluateZero_pauli_attachZero,if_neg hs,evaluateZero_attachZero] at he
      have hq : Q.run (fun _ => 1)=0 := hWi (by simpa using he.symm)
      exact pauli_one_ne_zero Q hq
    refine ⟨logicalPauli e R,?_⟩
    intro f
    have he := congrArg (evaluateZero e) (hR f)
    rw [hfactor,hfactor,evaluateZero_pauli_attachZero,if_pos hs,evaluateZero_attachZero] at he
    exact he

end
end Holant.Platonic.StabilizerErasure
