import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoActualSource

/-! Exact canonical support of the literal rank-two essential restriction.
A genuinely present third bundle enforces its affine relation; no parity
vertex is inserted. Every original signed multiplicity is retained upstream. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoSupport
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSignedPortsCore
open OrdinaryNegativeRankTwoPorts
open scoped BigOperators
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
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

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)

def essential : Signature AlgebraicComplex 3 := fun z=>f (word (port D) z)

theorem word_free (z : Fin 3→Bool) (j : Fin 2) :
    word (port D) z (D.ports j)=z (Fin.castLE (by decide : 2≤3) j) := by
  simp [word,port_free]

theorem bundle_present (j : Fin 3) (h : 0<I.bundleSize (port D) j) :
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

theorem supported_relation (present : 0<I.bundleSize (port D) 2)
    (z : Fin 3→Bool) (hz : essential D z≠0) : z 2=(z 0 ^^ z 1) := by
  obtain ⟨i,s,hi⟩ := bundle_present D 2 present
  have hc := D.covers (word (port D) z) hz
  have hd : (fun j : Fin 2=>word (port D) z (D.ports j))=![z 0,z 1] := by
    funext j
    rw [word_free]
    fin_cases j <;> rfl
  rw [hd] at hc
  rw [←word_code] at hc
  have hh := congrFun hc i
  simp only [word,hi,A.codeThree,Matrix.cons_val_two] at hh
  cases s <;> simpa using hh.symm

theorem code_of_relation (z : Fin 3→Bool) (h : z 2=(z 0 ^^ z 1)) :
    z=A.codeThree ![z 0,z 1] := by
  funext j
  fin_cases j <;> simp [A.codeThree,h]

theorem value (present : 0<I.bundleSize (port D) 2) (z : Fin 3→Bool) :
    essential D z=if z 2=(z 0 ^^ z 1) then f (D.encode ![z 0,z 1]) else 0 := by
  by_cases h : z 2=(z 0 ^^ z 1)
  · rw [if_pos h]
    unfold essential
    conv_lhs => rw [code_of_relation z h,word_code]
  · rw [if_neg h]
    exact not_ne_iff.mp (fun hn=>h (supported_relation D present z hn))

theorem support_iff (present : 0<I.bundleSize (port D) 2) (z : Fin 3→Bool) :
    essential D z≠0 ↔ z 2=(z 0 ^^ z 1) := by
  rw [value D present]
  by_cases h : z 2=(z 0 ^^ z 1) <;> simp [h,D.supported]

theorem square (h : Affine (fun x=>f x^2)) :
    Affine (fun z=>essential D z^2) := h.precompose _ (word_affine (port D))

/-- The exact support chart of the computed ternary row, selected at its two
literal first coordinates. Useful for transferring the reduced alpha class. -/
def chart (present : 0<I.bundleSize (port D) 2) : SystematicSupport (essential D) 2 where
  ports := fun j=>Fin.castLE (by decide : 2≤3) j
  injective := by intro a b h;exact Fin.ext (congrArg (fun i : Fin 3=>i.val) h)
  encode := A.codeThree
  affine := A.codeThree_affine
  free := by intro z j;fin_cases j <;> rfl
  supported := by intro z;change f (word (port D) (A.codeThree z))≠0;rw [word_code];exact D.supported z
  covers := by
    intro z hz
    have hr := (support_iff D present z).mp hz
    have hp : (fun i : Fin 2=>z (Fin.castLE (by decide : 2≤3) i))=![z 0,z 1] := by
      funext i;fin_cases i <;> rfl
    rw [hp]
    exact (code_of_relation z hr).symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoSupport
end
