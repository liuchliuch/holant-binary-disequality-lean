import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreePorts

/-! Exact seven-name support only when all seven original bundles really
occur. The converse code relation is derived from actual port representatives
and the original chart's coverage, never imposed as a virtual XOR vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeSupport
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSignedPortsCore
open OrdinaryNegativeSparseRankThreePorts
open scoped BigOperators
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m : ℕ}

theorem word_affine (p : Fin n→Port m) : TwoTranslate.IsAffineMap (word p) := by
  intro x y
  funext i
  cases h : p i with
  | inl b=>cases b <;> simp [word,h,AffinePhase.xor,AffinePhase.origin]
  | inr t=>
      rcases t with ⟨j,s⟩
      cases s <;> cases hx : x j <;> cases hy : y j <;>
        simp [word,h,hx,hy,AffinePhase.xor,AffinePhase.origin]

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)

def essential : Signature AlgebraicComplex 7 := fun z=>f (word (port D) z)

theorem port_free (j : Fin 3) : port D (D.ports j)=.inr (Fin.castLE (by decide : 3≤7) j,false) := by
  fin_cases j <;> simp [port,rawName,D.free,AffinePhase.origin,AffinePhase.basis,P.name]

theorem word_free (z : Fin 7→Bool) (j : Fin 3) :
    word (port D) z (D.ports j)=z (Fin.castLE (by decide : 3≤7) j) := by
  simp [word,port_free]

theorem bundle_present (j : Fin 7) (h : 0<I.bundleSize (port D) j) :
    ∃i : Fin n,∃s : Bool,port D i=.inr (j,s) := by
  unfold I.bundleSize at h
  obtain ⟨i,_,hi⟩ := Finset.sum_pos_iff.mp h
  cases hp : port D i with
  | inl b=>simp [hp] at hi
  | inr t=>
      rcases t with ⟨k,s⟩
      by_cases hk : k=j
      · subst k;exact ⟨i,s,hp⟩
      · simp [hp,hk] at hi

theorem supported_relation (present : ∀j,0<I.bundleSize (port D) j)
    (z : Fin 7→Bool) (hz : essential D z≠0) : z=A.codeSeven ![z 0,z 1,z 2] := by
  have hc := D.covers (word (port D) z) hz
  have hd : (fun j : Fin 3=>word (port D) z (D.ports j))=![z 0,z 1,z 2] := by
    funext j
    rw [word_free]
    fin_cases j <;> rfl
  rw [hd,←word_code] at hc
  funext j
  obtain ⟨i,s,hi⟩ := bundle_present D j (present j)
  have hh := congrFun hc i
  simp only [word,hi] at hh
  cases s <;> simpa using hh.symm

theorem value (present : ∀j,0<I.bundleSize (port D) j) (z : Fin 7→Bool) :
    essential D z=if z=A.codeSeven ![z 0,z 1,z 2] then f (D.encode ![z 0,z 1,z 2]) else 0 := by
  classical
  by_cases h : z=A.codeSeven ![z 0,z 1,z 2]
  · rw [if_pos h]
    unfold essential
    conv_lhs => rw [h,word_code]
  · rw [if_neg h]
    exact not_ne_iff.mp (fun hn=>h (supported_relation D present z hn))

theorem support_iff (present : ∀j,0<I.bundleSize (port D) j) (z : Fin 7→Bool) :
    essential D z≠0 ↔ z=A.codeSeven ![z 0,z 1,z 2] := by
  rw [value D present]
  constructor
  · intro hz
    by_contra h
    rw [if_neg h] at hz
    exact hz rfl
  · intro h
    rw [if_pos h]
    exact D.supported _

theorem essential_nonaffine (squareF : Affine (fun x=>f x^2)) (nonzero : f≠0) (bad : ¬Affine f) :
    ¬Affine (essential D) := by
  intro h
  apply D.nonAffine_reduced squareF nonzero bad
  convert h.precompose A.codeSeven A.codeSeven_affine using 1
  funext x
  unfold essential SystematicSupport.reduced
  rw [word_code]

theorem square (h : Affine (fun x=>f x^2)) :
    Affine (fun z=>essential D z^2) := h.precompose _ (word_affine (port D))

/-- All seven literal bundle witnesses justify the complete support chart. -/
def chart (present : ∀j,0<I.bundleSize (port D) j) : SystematicSupport (essential D) 3 where
  ports := fun j=>Fin.castLE (by decide : 3≤7) j
  injective := by intro a b h;exact Fin.ext (congrArg (fun i : Fin 7=>i.val) h)
  encode := A.codeSeven
  affine := A.codeSeven_affine
  free := by intro z j;fin_cases j <;> rfl
  supported := by intro z;change f (word (port D) (A.codeSeven z))≠0;rw [word_code];exact D.supported z
  covers := by
    intro z hz
    have hr := supported_relation D present z hz
    have hp : (fun i : Fin 3=>z (Fin.castLE (by decide : 3≤7) i))=![z 0,z 1,z 2] := by
      funext i;fin_cases i <;> rfl
    rw [hp]
    exact hr.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeSupport
end
