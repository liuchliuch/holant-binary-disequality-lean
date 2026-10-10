import Holant.Certificates.EqualityQuaternary.KleinOrbitData
import Holant.Certificates.EqualityQuaternary.ExoticPlane

/-! The representative-plane equations are homogeneous literal table
equations. They survive arbitrary actual scalar factors and linear sums.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein.Orbit
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Finite
set_option backward.isDefEq.respectTransparency false

def expected {K : Type*} [Zero K] (q : Signature K 4) (w : Fin 4 → Bool) : K :=
  if parity w then 0 else if w 0=w 3 then q (fun _ => false) else q ![false,false,true,true]
def Representative {K : Type*} [Zero K] (q : Signature K 4) : Prop := ∀ w,q w=expected q w

theorem representative_combination (c : Fin 4 → Scalar) (q : Fin 4 → Signature Scalar 4)
    (h : ∀ r,Representative (q r)) : Representative (fun w => ∑ r : Fin 4,c r*q r w) := by
  intro w
  unfold expected
  split_ifs with hp hb
  · apply Finset.sum_eq_zero
    intro r _
    have hh := h r w
    simp only [expected,hp,ite_true] at hh
    rw [hh,mul_zero]
  · apply Finset.sum_congr rfl
    intro r _
    have hh := h r w
    simpa only [expected,hp,hb,Bool.false_eq_true,ite_false,ite_true] using congrArg (fun z => c r*z) hh
  · apply Finset.sum_congr rfl
    intro r _
    have hh := h r w
    simpa only [expected,hp,hb,Bool.false_eq_true,ite_false,ite_true] using congrArg (fun z => c r*z) hh

theorem representative_smul (c : Scalar) {q : Signature Scalar 4} (h : Representative q) :
    Representative (c • q) := by
  intro w
  change c*q w=expected (c • q) w
  rw [h w]
  unfold expected
  split_ifs <;> simp

theorem representative_embed {q : Signature Q 4} (h : Representative q) :
    Representative (fun w => embed (q w)) := by
  intro w
  change embed (q w)=expected (fun w => embed (q w)) w
  rw [h w]
  unfold expected
  split_ifs <;> simp

def OrbitCheck (j : Fin 24) : Prop := ∀ (r : Fin 4) (i : Fin 16),
  run (basisQ .exotic) (paths j) (planeTensorQ .exotic j r) (word i)=
    expected (run (basisQ .exotic) (paths j) (planeTensorQ .exotic j r)) (word i)

theorem orbit_checked (j : Fin 24) (h : OrbitCheck j) (r : Fin 4) :
    Representative (run (E .exotic) (paths j) (planeTensor .exotic j r)) := by
  have hQ : Representative (run (basisQ .exotic) (paths j) (planeTensorQ .exotic j r)) := by
    intro w
    obtain ⟨i,rfl⟩ := words_complete w
    exact h r i
  have hh := representative_embed hQ
  rw [run_embed] at hh
  have he : (fun w => embed (planeTensorQ .exotic j r w))=planeTensor .exotic j r :=
    funext (fun w => (planeTensor_embed .exotic j r w).symm)
  rwa [he] at hh

/-- The table equations yield the source's explicit a,b coefficients from
the actual endpoint and 0011 entries, without an existential normal-form oracle. -/
theorem representative_plane {q : Signature Scalar 4} (h : Representative q) :
    q=Exotic.plane ((q (fun _ => false)+q ![false,false,true,true])/2)
      ((q ![false,false,true,true]-q (fun _ => false))/4) := by
  funext w
  rw [h w,Exotic.plane_table]
  unfold expected
  split_ifs <;> ring

end Holant.Certificates.EqualityQuaternary.Klein.Orbit
