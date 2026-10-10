import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSinglePairCocycle
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSinglePairCount

/-! All origin-through coordinate pins and one fixed equality hyperplane
determine a full Affine function in dimension at least four. The fourth
mixed difference propagates every remaining cube onto a zero pin face. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSinglePairStar
open Holant Holant.Tractable Holant.Tractable.AffinePhase
namespace C
export NoXGeneralSinglePairCocycle (swap_first swap_last shift_of_cross one_endpoint)
end C
namespace N
export NoXGeneralSinglePairCount (hit count hit_le outside)
end N
namespace S
export NoXLocalStarCriterion (zeroCut equalCut zero_ratio equal_ratio)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} (f : Signature AlgebraicComplex n) (full : ∀x,f x≠0)
variable (pins : ∀p,Affine (S.zeroCut f p))
variable (p q : Fin n) (pq : p≠q) (pair : Affine (S.equalCut f p q))

include pair in
theorem pair_reverse : Affine (S.equalCut f q p) := by
  convert pair using 1
  funext x
  simp only [S.equalCut,eq_comm]

include full pins pair in
theorem no_endpoint (z : Word n) (i j k : Fin n)
    (ip : i≠p) (iq : i≠q) (jp : j≠p) (jq : j≠q) (kp : k≠p) (kq : k≠q) :
    thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  by_cases hp : z p=false
  · exact S.zero_ratio f full p (pins p) _ _ _ _ hp
      (by simp [basis,Ne.symm ip]) (by simp [basis,Ne.symm jp]) (by simp [basis,Ne.symm kp])
  by_cases hq : z q=false
  · exact S.zero_ratio f full q (pins q) _ _ _ _ hq
      (by simp [basis,Ne.symm iq]) (by simp [basis,Ne.symm jq]) (by simp [basis,Ne.symm kq])
  exact S.equal_ratio f full p q pair _ _ _ _
    ((Bool.eq_true_of_not_eq_false hp).trans (Bool.eq_true_of_not_eq_false hq).symm)
    (by simp [basis,Ne.symm ip,Ne.symm iq]) (by simp [basis,Ne.symm jp,Ne.symm jq])
    (by simp [basis,Ne.symm kp,Ne.symm kq])

include full pins pq pair in
theorem first_endpoint (z : Word n) (i j k : Fin n) (hi : i=p ∨ i=q)
    (hj : ¬(j=p ∨ j=q)) (hk : ¬(k=p ∨ k=q)) :
    thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  rcases hi with hi|hi
  · subst i
    exact C.one_endpoint f full pins z p j k q (pair_reverse f p q pair)
      (Ne.symm (not_or.mp hj).1) (Ne.symm (not_or.mp hk).1) pq.symm
      (Ne.symm (not_or.mp hj).2) (Ne.symm (not_or.mp hk).2)
  · subst i
    exact C.one_endpoint f full pins z q j k p pair
      (Ne.symm (not_or.mp hj).2) (Ne.symm (not_or.mp hk).2) pq
      (Ne.symm (not_or.mp hj).1) (Ne.symm (not_or.mp hk).1)

include full pins pq pair in
theorem small_cube (z : Word n) (i j k : Fin n) (small : N.count p q i j k≤1) :
    thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  by_cases hi : i=p ∨ i=q
  · have hj : ¬(j=p ∨ j=q) := by intro h;simp [N.count,N.hit,hi,h] at small;omega
    have hk : ¬(k=p ∨ k=q) := by intro h;simp [N.count,N.hit,hi,h] at small
    exact first_endpoint f full pins p q pq pair z i j k hi hj hk
  by_cases hj : j=p ∨ j=q
  · have hk : ¬(k=p ∨ k=q) := by intro h;simp [N.count,N.hit,hj,h] at small
    rw [C.swap_first]
    exact first_endpoint f full pins p q pq pair z j i k hj hi hk
  by_cases hk : k=p ∨ k=q
  · rw [C.swap_last,C.swap_first]
    exact first_endpoint f full pins p q pq pair z k i j hk hi hj
  exact no_endpoint f full pins p q pair z i j k
    (not_or.mp hi).1 (not_or.mp hi).2 (not_or.mp hj).1 (not_or.mp hj).2
    (not_or.mp hk).1 (not_or.mp hk).2

include full pins pq pair in
theorem cubes (higher : 4≤n) (z : Word n) (i j k : Fin n) :
    thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  have all : ∀t : ℕ,∀z : Word n,∀i j k : Fin n,N.count p q i j k=t→
      thirdRatio f z (basis i) (basis j) (basis k)=1 := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih=>
      intro z i j k count
      by_cases small : t≤1
      · exact small_cube f full pins p q pq pair z i j k (by omega)
      have first (z : Word n) (i j k : Fin n) (hi : i=p ∨ i=q) (count : N.count p q i j k=t) :
          thirdRatio f z (basis i) (basis j) (basis k)=1 := by
        obtain ⟨r,rp,rq,ri,rj,rk⟩:=N.outside p q higher i j k hi (by omega)
        have lower : N.count p q r j k<t := by
          simp only [N.count,N.hit,ite_eq_left hi,ite_eq_right (not_or.mpr ⟨rp,rq⟩)] at count ⊢
          omega
        have cross (w : Word n) : thirdRatio f w (basis r) (basis j) (basis k)=1 :=
          ih (N.count p q r j k) lower w r j k rfl
        let base : Word n:=Function.update z r false
        have zero : thirdRatio f base (basis i) (basis j) (basis k)=1 :=
          S.zero_ratio f full r (pins r) _ _ _ _ (by simp [base])
            (by simp [basis,ri]) (by simp [basis,rj]) (by simp [basis,rk])
        have shifted:=C.shift_of_cross f full base (basis r) (basis i) (basis j) (basis k)
          (cross base) (cross (xor base (basis i)))
        rw [zero] at shifted
        cases hr : z r with
        | false=>
            have he : base=z := by simp [base,←hr]
            simpa only [he] using zero
        | true=>
            have he : xor base (basis r)=z := by
              funext v
              by_cases hv : v=r
              · subst v;simp [AffinePhase.xor,basis,base,hr]
              · simp [AffinePhase.xor,basis,base,hv]
            simpa only [he] using shifted
      by_cases hi : i=p ∨ i=q
      · exact first z i j k hi count
      by_cases hj : j=p ∨ j=q
      · rw [C.swap_first]
        exact first z j i k hj (by simpa only [NoXGeneralSinglePairCount.swap_first] using count)
      have bound:=N.hit_le p q k
      simp only [N.hit] at bound
      simp only [N.count,N.hit,ite_eq_right hi,ite_eq_right hj,zero_add] at count
      omega
  exact all _ z i j k rfl

include full pins pq pair in
theorem affine (higher : 4≤n) : Affine f :=
  OrdinaryNegativeAffineThreeFaces.affine_of_coordinate_cubes f full (cubes f full pins p q pq pair higher)

include full pq in
theorem bad_cut (higher : 4≤n) (bad : ¬Affine f) :
    (∃i,¬Affine (S.zeroCut f i)) ∨ ¬Affine (S.equalCut f p q) := by
  classical
  by_contra h
  push Not at h
  exact bad (affine f full h.1 p q pq h.2 higher)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSinglePairStar
end
