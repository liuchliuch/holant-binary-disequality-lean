import Holant.Certificates.EqualityQuaternary.C2BlockEquations
import Holant.Projective.CyclicQuaternary.PhysicalSource

/-! The original physical C2 deck implies the Walsh parity and every
complementary-block equation used by A.7. Scalars are cancelled only in
the analytic proof; no Walsh tensor is asserted physically realizable. -/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat
open Holant.Projective.CyclicPhasePencil (diagonal Z)
set_option backward.isDefEq.respectTransparency false

def binary (p : Bool) : Mat := if p then Signature.disequality else Signature.equality
def sign (p : Bool) : Scalar := if p then -1 else 1

structure Representatives (F : SignatureFamily Scalar) where
  matrix : Bool → Mat
  multiplier : Bool → Scalar
  multiplier_ne_zero : ∀ p, multiplier p ≠ 0
  actual : ∀ p, Gadget.Realizes F .disequality (kernelSignature (matrix p))
  normal_form : ∀ p, matrix p = scale (multiplier p) (binary p)

def ActualLine {F : SignatureFamily Scalar} (reps : Representatives F) (B : Mat) : Prop :=
  ∃ p c, c≠0 ∧ B=scale c (reps.matrix p)

def PhysicalDeck {F : SignatureFamily Scalar} (reps : Representatives F)
    (q : Signature Scalar 4) : Prop :=
  ∀ (i : Fin 3) (side order p : Bool),
    orderedPhysicalCard q i side order (reps.matrix p)=0 ∨
      ActualLine reps (orderedPhysicalCard q i side order (reps.matrix p))

def WalshSafe (B : Mat) : Prop :=
  B false true=0 ∧ B true false=0 ∧ (B true true)^2=(B false false)^2

theorem walshSafe_scale_iff (c : Scalar) (hc : c≠0) (B : Mat) :
    WalshSafe (scale c B) ↔ WalshSafe B := by
  unfold WalshSafe scale
  simp only [mul_eq_zero,hc,false_or,mul_pow]
  exact and_congr_right (fun _ => and_congr_right (fun _ =>
    ⟨mul_left_cancel₀ (pow_ne_zero 2 hc),fun h => congrArg (fun z => c^2*z) h⟩))

theorem walsh_binary_scale (c : Scalar) (p : Bool) :
    walshBinary (scale c (binary p)) = scale (c/2) (diagonal 1 (sign p)) := by
  funext a b
  cases p <;> cases a <;> cases b <;>
    simp [walshBinary,Pinv,P,Kernel.mul_apply,Kernel.transpose,binary,scale,
      Signature.equality,Signature.disequality,diagonal,sign] <;> ring

theorem safe_of_actual {F : SignatureFamily Scalar} (reps : Representatives F)
    {B : Mat} (h : B=0 ∨ ActualLine reps B) : WalshSafe (walshBinary B) := by
  rcases h with rfl | ⟨p,c,_,rfl⟩
  · simp [WalshSafe,walshBinary,Kernel.mul_apply]
  · rw [reps.normal_form]
    have he : scale c (scale (reps.multiplier p) (binary p)) =
        scale (c*reps.multiplier p) (binary p) := by funext a b; simp [scale,mul_assoc]
    rw [he,walsh_binary_scale]
    cases p <;> simp [WalshSafe,scale,diagonal,sign]

def walshCard (q : Signature Scalar 4) (i : Fin 3) (side p : Bool) : Mat :=
  contractKernel q i side (diagonal 1 (sign p))

theorem walshCard_apply (q : Signature Scalar 4) (i : Fin 3) (side p u v : Bool) :
    walshCard q i side p u v =
      q (join i side false false u v) + sign p*q (join i side true true u v) := by
  simp [walshCard,contractKernel,diagonal,add_comm]

theorem physical_normalization {F : SignatureFamily Scalar} (reps : Representatives F)
    (q : Signature Scalar 4) (i : Fin 3) (side p : Bool) :
    walshBinary (physicalCard q i side (reps.matrix p)) =
      scale (2*reps.multiplier p) (walshCard (walsh q) i side p) := by
  rw [walsh_physicalCard,reps.normal_form,walsh_binary_scale]
  funext u v
  cases p <;>
    simp [contractKernel,walshCard,Kernel.mul_apply,scale,diagonal,
      Projective.CyclicPhasePencil.Z,sign] <;> ring

theorem physical_walshSafe {F : SignatureFamily Scalar} (reps : Representatives F)
    (q : Signature Scalar 4) (hdeck : PhysicalDeck reps q)
    (i : Fin 3) (side p : Bool) : WalshSafe (walshCard (walsh q) i side p) := by
  have h := safe_of_actual reps (hdeck i side false p)
  change WalshSafe (walshBinary (physicalCard q i side (reps.matrix p))) at h
  rw [physical_normalization] at h
  exact (walshSafe_scale_iff _ (mul_ne_zero (by norm_num) (reps.multiplier_ne_zero p)) _).mp h

theorem odd_coefficients_zero (a : Signature Scalar 4)
    (hs : ∀ (i : Fin 3) (side p : Bool), WalshSafe (walshCard a i side p)) : EvenSupported a := by
  have hz (i : Fin 3) (side u : Bool) :
      a (join i side false false u (!u))=0 ∧ a (join i side true true u (!u))=0 := by
    have hp : walshCard a i side false u (!u)=0 := by
      cases u
      · exact (hs i side false).1
      · exact (hs i side false).2.1
    have hm : walshCard a i side true u (!u)=0 := by
      cases u
      · exact (hs i side true).1
      · exact (hs i side true).2.1
    rw [walshCard_apply] at hp hm
    simp only [sign,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul] at hp hm
    constructor
    · linear_combination (hp+hm)/2
    · linear_combination (hp-hm)/2
  intro w hw
  have he : w = ![w 0,w 1,w 2,w 3] := by funext i; fin_cases i <;> rfl
  rw [he]
  have h00 := hz 0 false false
  have h01 := hz 0 false true
  have h10 := hz 0 true false
  have h11 := hz 0 true true
  clear he hs hz
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp_all [odd,join]

theorem safe_blocks (a : Signature Scalar 4)
    (hs : ∀ (i : Fin 3) (side p : Bool), WalshSafe (walshCard a i side p)) :
    ∀ i, SafeBlock (endpoint0 a) (endpoint1 a) (coordinates a i).1 (coordinates a i).2 := by
  intro i
  have h1 := (hs i false false).2.2
  have h2 := (hs i false true).2.2
  have h3 := (hs i true false).2.2
  have h4 := (hs i true true).2.2
  rw [walshCard_apply,walshCard_apply] at h1 h2 h3 h4
  fin_cases i <;>
    simpa [SafeBlock,endpoint0,endpoint1,coordinates,join,sign,sub_eq_add_neg] using
      And.intro h1 (And.intro h2 (And.intro h3 h4))

/-- The C2 physical inputs derive every Walsh restriction used before the
common-sign/mixed-sign case split, rather than taking those restrictions as input. -/
theorem source_C2_walsh_equations {F : SignatureFamily Scalar} (reps : Representatives F)
    (q : Signature Scalar 4) (hdeck : PhysicalDeck reps q) :
    EvenSupported (walsh q) ∧ ∀ i,
      BlockRelations (endpoint0 (walsh q)) (endpoint1 (walsh q))
        (coordinates (walsh q) i).1 (coordinates (walsh q) i).2 := by
  have hs := physical_walshSafe reps q hdeck
  exact ⟨odd_coefficients_zero _ hs,fun i => (safeBlock_iff _ _ _ _).mp (safe_blocks _ hs i)⟩

end Holant.Certificates.EqualityQuaternary.C2
