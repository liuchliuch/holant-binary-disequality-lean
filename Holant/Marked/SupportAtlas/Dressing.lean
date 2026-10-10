import Holant.Marked.Dictionary
import Holant.Marked.SupportAtlas.Boolean
import Holant.Projective.CyclicDressing.Realization

/-! Actual sector-X dressing over the original retained signature family.
The analytic basis is transported symbolically and is never used as a gadget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Holant.Marked.SupportAtlas
open Holant.Tractable
open Holant.Projective.CyclicDressing
open Holant.Projective.CyclicQuaternary.Physical (sum_words4)

def xorWord (x mask : Word) : Word := fun i => x i ^^ mask i

theorem sector_onePort_action (U : InvertibleKernel) (q : Signature Scalar 4) (B : Mat)
    (i : Fin 4) : U.symm.action (onePort q i B) =
      Signature.coordinateAction (fun j => if j = i then sectorTransfer U B else Signature.equality)
        (U.symm.action q) := by
  have hq := U.action_symm_action q
  calc
    _ = U.symm.action (onePort (U.action (U.symm.action q)) i B) := by rw [hq]
    _ = _ := by
      simp only [InvertibleKernel.action, InvertibleKernel.symm, onePort,
        Signature.coordinateAction_comp]
      congr 1
      funext j
      by_cases hj : j = i
      · simp only [hj, ↓reduceIte]
        simp [sectorTransfer, conjugate, InvertibleKernel.symm, Kernel.mul_assoc]
      · simp [hj, U.matrix_inverse]

theorem one_flip_action (q : Signature Scalar 4) (c : Scalar) (i : Fin 4) (x : Word) :
    Signature.coordinateAction (fun j => if j = i then scale c Signature.disequality
      else Signature.equality) q x = c * q (Function.update x i (!(x i))) := by
  have hx : x = ![x 0,x 1,x 2,x 3] := by funext j; fin_cases j <;> rfl
  rw [hx]
  fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Signature.coordinateAction, sum_words4, Fin.prod_univ_succ, scale,
      Signature.disequality, Signature.equality, update_word4, h0,h1,h2,h3]

def dressAt (q : Signature Scalar 4) (B : Mat) (mask : Word) (i : Fin 4) : Signature Scalar 4 :=
  if mask i then onePort q i B else q

def dressMask (q : Signature Scalar 4) (B : Mat) (mask : Word) : Signature Scalar 4 :=
  dressAt (dressAt (dressAt (dressAt q B mask 0) B mask 1) B mask 2) B mask 3

def dressingMultiplier (c : Scalar) (mask : Word) : Scalar := ∏ i, if mask i then c else 1

theorem sector_dressAt (U : InvertibleKernel) (q : Signature Scalar 4) (B : Mat)
    (c : Scalar) (hB : sectorTransfer U B = scale c Signature.disequality)
    (mask : Word) (i : Fin 4) (x : Word) :
    U.symm.action (dressAt q B mask i) x = (if mask i then c else 1) *
      U.symm.action q (Function.update x i (x i ^^ mask i)) := by
  cases hm : mask i
  · simp [dressAt, hm]
  · rw [dressAt, hm]
    simp only [↓reduceIte]
    rw [sector_onePort_action, hB, one_flip_action]
    simp

theorem dressingMultiplier_ne_zero (c : Scalar) (hc : c ≠ 0) (mask : Word) :
    dressingMultiplier c mask ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  cases mask i <;> simp [hc]

/-- Every selected port contributes its actual representative scalar once. -/
theorem sector_dressMask (U : InvertibleKernel) (q : Signature Scalar 4) (B : Mat)
    (c : Scalar) (hB : sectorTransfer U B = scale c Signature.disequality)
    (mask : Word) (x : Word) :
    U.symm.action (dressMask q B mask) x =
      dressingMultiplier c mask * U.symm.action q (xorWord x mask) := by
  simp only [dressMask, sector_dressAt U _ B c hB]
  have he : Function.update
      (Function.update (Function.update (Function.update x 3 (x 3 ^^ mask 3)) 2 (x 2 ^^ mask 2))
        1 (x 1 ^^ mask 1)) 0 (x 0 ^^ mask 0) = xorWord x mask := by
    funext j; fin_cases j <;> simp [xorWord, Function.update_apply]
  simp only [Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3),
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
    Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
    Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3)]
  rw [he]
  simp only [dressingMultiplier, Fin.prod_univ_four]
  ring

theorem realizes_dressAt (F : SignatureFamily Scalar) (q : Signature Scalar 4) (B : Mat)
    (hq : Gadget.Realizes F .disequality q)
    (hB : Gadget.Realizes F .disequality (kernelSignature B)) (mask : Word) (i : Fin 4) :
    Gadget.Realizes F .disequality (dressAt q B mask i) := by
  cases hm : mask i
  · simpa [dressAt, hm] using hq
  · simpa [dressAt, hm] using realizes_onePort F q B hq hB i

/-- Physical construction uses four disjoint one-port joins, retaining the same family. -/
theorem realizes_dressMask (F : SignatureFamily Scalar) (q : Signature Scalar 4) (B : Mat)
    (hq : Gadget.Realizes F .disequality q)
    (hB : Gadget.Realizes F .disequality (kernelSignature B)) (mask : Word) :
    Gadget.Realizes F .disequality (dressMask q B mask) := by
  exact realizes_dressAt F _ B (realizes_dressAt F _ B
    (realizes_dressAt F _ B (realizes_dressAt F q B hq hB mask 0) hB mask 1) hB mask 2) hB mask 3

end Holant.Marked.SupportAtlas
