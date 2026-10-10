import Holant.Proofs.Closure.ClosureSixPortParity
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist

/-! NEW UNVERIFIED direct proper splits from literal zero/proportional sectors.
All endpoints are the given tensor's raw slices. The target factor and exact
ordered 2+4 split are built internally; no FourProducts or atlas is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective
open Holant.LocalDrafts.FinitePGL2.Stabilization

abbrev Mat := Kernel ℂ
def orderedWord (e : Equiv.Perm (Fin 6)) (a b : Bool) (x : Word 4) : Word 6 :=
  fillSix e a (a ^^ b) x
def binaryWord (U : Mat) : Signature ℂ 2 := fun x => U (x 0) (x 1)

theorem orderedWord_reconstruct (e : Equiv.Perm (Fin 6)) (w : Word 6) :
    orderedWord e (w (e 0)) (w (e 1)) (residualSix e w) = w :=
  fillSix_reconstruct e w

theorem rightPort (i : Fin 4) :
    (finSumFinEquiv (.inr i) : Fin (2+4)) = i.succ.succ := by
  apply Fin.ext
  simp only [finSumFinEquiv_apply_right,Fin.val_natAdd,Fin.val_succ]
  omega

/-- Exact pointwise factor equations yield a literal proper ordered 2+4
split, with the SAME original deleted pair and no scalar loss. -/
def splitTwoFour (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (U : Mat)
    (B : Signature ℂ 4)
    (slices : ∀ a b x, h (orderedWord e a b x) = U a b * B x) :
    ProperSplit (⟨6,h⟩ : AnySignature ℂ) ⟨2,binaryWord U⟩ ⟨4,B⟩ where
  left_pos := by norm_num
  right_pos := by norm_num
  ports := finSumFinEquiv.trans e
  scale := 1
  equation := by
    funext w
    have hw := slices (w (e 0)) (w (e 1)) (residualSix e w)
    rw [orderedWord_reconstruct] at hw
    have leftZero : Fin.castAdd 4 (0 : Fin 2) = (0 : Fin 6) := rfl
    have leftOne : Fin.castAdd 4 (1 : Fin 2) = (1 : Fin 6) := rfl
    simp only [Units.val_one,one_mul,binaryWord,Equiv.trans_apply,
      finSumFinEquiv_apply_left,leftZero,leftOne,rightPort]
    convert hw using 1
    rfl

def ZeroSector (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool) : Prop :=
  sliceSix h e p false = 0 ∧ sliceSix h e p true = 0

def DependentEndpoints (A B : Signature ℂ 4) : Prop :=
  (∃ c : ℂ, B = c • A) ∨ ∃ c : ℂ, A = c • B

/-- A whole sampled zero pencil forces BOTH analytic endpoints zero. This
includes m=3 and does not require two selected nonzero samples. -/
theorem zeroSector_of_all_root_samples {m : ℕ} (hm : 3 ≤ m)
    (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (zero : ∀ t : ℂ, t^m=1 → phaseCard h e p t = 0) : ZeroSector h e p := by
  have endpoints (x : Word 4) :
      sliceSix h e p false x = 0 ∧ sliceSix h e p true x = 0 := by
    have hz := affine_product_zero_on_rootPolygon hm
      (sliceSix h e p false x) (sliceSix h e p true x) 1 0 (by
        intro t ht
        have := congrFun (zero t ht) x
        simpa only [phaseCard,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
          Pi.zero_apply,mul_zero,add_zero,mul_one] using this)
    exact hz.resolve_right (fun hh => one_ne_zero hh.1)
  exact ⟨funext (fun x => (endpoints x).1),funext (fun x => (endpoints x).2)⟩

private theorem factorSlices_left (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6))
    (p : Bool) (zero : ZeroSector h e p) (c : ℂ)
    (dependent : sliceSix h e (!p) true = c • sliceSix h e (!p) false) :
    ∀ a b x, h (orderedWord e a b x) =
      Holant.Dihedral.EndpointParallelogram.phaseKernel (!p) c a b *
        sliceSix h e (!p) false x := by
  intro a b x
  have z0 := congrFun zero.1 x
  have z1 := congrFun zero.2 x
  have dep := congrFun dependent x
  cases p <;> cases a <;> cases b <;>
    simp only [orderedWord,fillSix,Holant.Dihedral.EndpointParallelogram.phaseKernel,
      Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,reduceCtorEq,ite_true,ite_false,zero_mul,one_mul] <;>
    first
    | simpa only [sliceSix,fillSix,Bool.false_xor,Bool.true_xor,Bool.not_false,
        Bool.not_true,Pi.zero_apply] using z0
    | simpa only [sliceSix,fillSix,Bool.false_xor,Bool.true_xor,Bool.not_false,
        Bool.not_true,Pi.zero_apply] using z1
    | simpa only [sliceSix,fillSix,Bool.false_xor,Bool.true_xor,Bool.not_false,
        Bool.not_true,Pi.smul_apply,smul_eq_mul] using dep
    | rfl

/-- One raw parity sector vanishes and the other is proportional: the actual
2+4 factor is selected from a raw endpoint, not supplied by a sector classifier. -/
theorem zero_proportional_split (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (zero : ZeroSector h e p)
    (dependent : DependentEndpoints (sliceSix h e (!p) false) (sliceSix h e (!p) true)) :
    ∃ U : Mat, ∃ B : Signature ℂ 4,
      Nonempty (ProperSplit (⟨6,h⟩ : AnySignature ℂ) ⟨2,binaryWord U⟩ ⟨4,B⟩) := by
  rcases dependent with ⟨c,he⟩ | ⟨c,he⟩
  · exact ⟨Holant.Dihedral.EndpointParallelogram.phaseKernel (!p) c,
      sliceSix h e (!p) false,⟨splitTwoFour h e _ _ (factorSlices_left h e p zero c he)⟩⟩
  · let U : Mat := fun a b =>
      if (a ^^ b) = (!p) then (if a then 1 else c) else 0
    have slices : ∀ a b x, h (orderedWord e a b x) = U a b * sliceSix h e (!p) true x := by
      intro a b x
      have z0 := congrFun zero.1 x
      have z1 := congrFun zero.2 x
      have dep := congrFun he x
      cases p <;> cases a <;> cases b <;>
        simp only [U,orderedWord,fillSix,Bool.false_xor,Bool.true_xor,Bool.not_false,
          Bool.not_true,Bool.false_eq_true,reduceCtorEq,ite_true,ite_false,zero_mul,one_mul] <;>
        first
        | simpa only [sliceSix,fillSix,Bool.false_xor,Bool.true_xor,Bool.not_false,
            Bool.not_true,Pi.zero_apply] using z0
        | simpa only [sliceSix,fillSix,Bool.false_xor,Bool.true_xor,Bool.not_false,
            Bool.not_true,Pi.zero_apply] using z1
        | simpa only [sliceSix,fillSix,Bool.false_xor,Bool.true_xor,Bool.not_false,
            Bool.not_true,Pi.smul_apply,smul_eq_mul] using dep
        | rfl
    exact ⟨U,sliceSix h e (!p) true,⟨splitTwoFour h e U _ slices⟩⟩

theorem zero_proportional_not_prime (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (zero : ZeroSector h e p)
    (dependent : DependentEndpoints (sliceSix h e (!p) false) (sliceSix h e (!p) true)) :
    ¬ Prime (⟨6,h⟩ : AnySignature ℂ) := by
  obtain ⟨U,B,split⟩ := zero_proportional_split h e p zero dependent
  exact fun hp => hp.2 ⟨⟨2,binaryWord U⟩,⟨4,B⟩,split⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
