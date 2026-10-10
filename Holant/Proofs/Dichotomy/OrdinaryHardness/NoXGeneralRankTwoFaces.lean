import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoMinimalLines
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedProjection

/-! Literal signed-port maps for all four proper coordinate faces of a
rank-two support, including reversal of their remaining variable. Separate
positive/negative counts and full affine correction values are both exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoFaces
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXSeparateSignedProjection (signedCount)
end P
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeSparseMixingAlpha (codeThree)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false

def axis (i : Fin 4) : Fin 2 := ![0,0,1,1] i
def outside (i : Fin 4) : Bool := ![false,true,false,true] i

def line (i : Fin 4) (reverse t : Bool) : Word 2 :=
  if axis i=0 then ![reverse ^^ t,outside i] else ![outside i,reverse ^^ t]

variable {n : ℕ} (p : Fin n→Port 3)
def ports (i : Fin 4) (target : Fin 3) (reverse : Bool) : Fin n→Port 3 := fun k=>
  match p k with
  | .inl b=>.inl b
  | .inr (j,s)=>if j=2 then .inr (target,s ^^ outside i ^^ reverse)
    else if j.val=(axis i).val then .inr (target,s ^^ reverse) else .inl (s ^^ outside i)

def lineCount (i : Fin 4) (bit : Bool) : ℕ :=
  ![P.signedCount p 0 bit+P.signedCount p 2 bit,
    P.signedCount p 0 bit+P.signedCount p 2 (!bit),
    P.signedCount p 1 bit+P.signedCount p 2 bit,
    P.signedCount p 1 bit+P.signedCount p 2 (!bit)] i

theorem word_value (i : Fin 4) (target : Fin 3) (reverse : Bool) (z : Word 3) :
    word (ports p i target reverse) z=word p (Q.codeThree (line i reverse (z target))) := by
  funext k
  cases hp : p k with
  | inl b=>simp [ports,OrdinaryNegativeSignedPortsCore.word,hp]
  | inr a=>
      rcases a with ⟨j,sgn⟩
      fin_cases i <;> fin_cases j <;> cases sgn <;> cases reverse <;> cases ht : z target <;>
        simp [ports,OrdinaryNegativeSignedPortsCore.word,line,axis,outside,Q.codeThree,hp,ht]

theorem signed_count (i : Fin 4) (target q : Fin 3) (reverse bit : Bool) :
    P.signedCount (ports p i target reverse) q bit=
      if target=q then lineCount p i (bit ^^ reverse) else 0 := by
  by_cases h : target=q
  · subst q
    rw [ite_eq_left rfl]
    fin_cases i <;> dsimp [lineCount]
    all_goals rw [P.signedCount,P.signedCount,P.signedCount,←Finset.sum_add_distrib]
    all_goals apply Finset.sum_congr rfl
    all_goals intro k _
    all_goals cases hp : p k with
      | inl b=>simp [ports,hp]
      | inr a=>
          rcases a with ⟨j,sgn⟩
          fin_cases j <;> cases sgn <;> cases reverse <;> cases bit <;> simp [ports,axis,outside,hp]
  · rw [ite_eq_right h]
    unfold P.signedCount
    apply Finset.sum_eq_zero
    intro k _
    cases hp : p k with
    | inl b=>simp [ports,hp]
    | inr a=>
        rcases a with ⟨j,sgn⟩
        have ne : ports p i target reverse k≠Sum.inr (q,bit) := by
          unfold ports
          rw [hp]
          dsimp only
          split_ifs <;> simp [h]
        exact ite_eq_right ne

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)

theorem original_word (i : Fin 4) (target : Fin 3) (reverse : Bool) (z : Word 3) :
    word (ports (Q.port D) i target reverse) z=D.encode (line i reverse (z target)) := by
  rw [word_value,Q.word_code]

theorem line_affine (i : Fin 4) (target : Fin 3) (reverse : Bool) :
    IsAffineMap (fun z : Word 3=>line i reverse (z target)) := by
  intro x y
  funext j
  fin_cases i <;> fin_cases j <;> cases reverse <;> cases hx : x target <;> cases hy : y target <;>
    simp [line,axis,outside,AffinePhase.xor,AffinePhase.origin,hx,hy]

theorem fixed (i : Fin 4) (reverse t : Bool) (j : Fin 2) (hj : j∉({axis i} : Finset (Fin 2))) :
    line i reverse t j=outside i := by
  fin_cases i <;> fin_cases j <;> simp_all [axis,outside,line]

variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Word 2,Affine (minor D S z))
include minimal in
theorem correction_affine (i : Fin 4) (target : Fin 3) (reverse : Bool) :
    Affine (fun z=>f (word (ports (Q.port D) i target reverse) z)) := by
  have face:=(face_affine_of_minor D {axis i} (fun _=>outside i) (minimal {axis i} (by simp) (fun _=>outside i))).precompose
    (fun z : Word 3=>line i reverse (z target)) (line_affine i target reverse)
  convert face using 1
  funext z
  rw [original_word]
  change f (D.encode (line i reverse (z target)))=
    if ∀j,j∉({axis i} : Finset (Fin 2))→line i reverse (z target) j=outside i then _ else 0
  rw [ite_eq_left (fun j hj=>fixed i reverse (z target) j hj)]
  rfl

theorem correction_full (i : Fin 4) (target : Fin 3) (reverse : Bool) (z : Word 3) :
    f (word (ports (Q.port D) i target reverse) z)≠0 := by
  rw [original_word]
  exact D.supported _


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankTwoFaces
end
