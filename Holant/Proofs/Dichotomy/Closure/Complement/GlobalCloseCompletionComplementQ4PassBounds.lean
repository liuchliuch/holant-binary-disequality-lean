import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Differences
import Holant.OneHot.ArithmeticSizeTree

/-! Each difference pass raises the arithmetic degree/summand budget only
by the root budget plus two. Repeated passes therefore have a linear budget
in their count, despite the exponentially many formal expanded terms. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PassBounds
open Holant.OneHot
namespace D
export GlobalCloseCompletionComplementQ4Differences (pass processList factor)
end D
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K A : Type} [Field K]
variable (coeff : A→K) (unit neg : A) (hone : coeff unit=1) (hneg : coeff neg= -1)

include hone hneg in
theorem difference {R Y : ℕ} {root a b : K} (hr : ArithmeticSize.Bound coeff R root)
    (ha : ArithmeticSize.Bound coeff Y a) (hb : ArithmeticSize.Bound coeff Y b) :
    ArithmeticSize.Bound coeff (Y+R+2) (b-root*a) := by
  have hn : ArithmeticSize.Bound coeff 1 (-1:K):=hneg ▸ ArithmeticSize.Bound.coefficient neg
  have hp : ArithmeticSize.Bound coeff (Y+R+1) (-(root*a)) := by
    simpa only [neg_one_mul,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hn.mul (hr.mul ha)
  have bound:= (hb.mono unit hone (by omega : Y≤Y+R+1)).add unit hone hp
  simpa only [sub_eq_add_neg,Nat.add_assoc] using bound

include hone hneg in
theorem pass_bound {R Y : ℕ} (root : K) (hr : ArithmeticSize.Bound coeff R root)
    (values : List K) (hv : ∀x∈values,ArithmeticSize.Bound coeff Y x) :
    ∀x∈D.pass root values,ArithmeticSize.Bound coeff (Y+R+2) x := by
  induction values with
  | nil=>simp [D.pass]
  | cons a values ih=>
    cases values with
    | nil=>simp [D.pass]
    | cons b values=>
      intro x member
      rcases List.mem_cons.mp member with same|rest
      · subst x
        exact difference coeff unit neg hone hneg hr (hv a (by simp)) (hv b (by simp))
      · exact ih (fun y hy=>hv y (by simp [hy])) x rest

include hone hneg in
theorem foldr_bound {R Y : ℕ} (roots values : List K)
    (hr : ∀x∈roots,ArithmeticSize.Bound coeff R x)
    (hv : ∀x∈values,ArithmeticSize.Bound coeff Y x) :
    ∀x∈roots.foldr D.pass values,ArithmeticSize.Bound coeff (Y+roots.length*(R+2)) x := by
  induction roots with
  | nil=>simpa using hv
  | cons root roots ih=>
    have old:=ih (fun r member=>hr r (by simp [member]))
    have next:=pass_bound coeff unit neg hone hneg root (hr root (by simp)) _ old
    intro x member
    have h:=next x member
    convert h using 1 <;> simp only [List.length_cons] <;> ring

include hone hneg in
theorem process_bound {R Y : ℕ} (roots values : List K)
    (hr : ∀x∈roots,ArithmeticSize.Bound coeff R x)
    (hv : ∀x∈values,ArithmeticSize.Bound coeff Y x) :
    ∀x∈D.processList roots values,ArithmeticSize.Bound coeff (Y+roots.length*(R+2)) x := by
  unfold D.processList
  rw [←List.foldr_reverse]
  simpa only [List.length_reverse] using foldr_bound coeff unit neg hone hneg roots.reverse values
    (fun x member=>hr x (List.mem_reverse.mp member)) hv

theorem pass_length (root : K) (values : List K) : (D.pass root values).length=values.length-1 := by
  induction values with
  | nil=>rfl
  | cons a values ih=>
    cases values with
    | nil=>rfl
    | cons b values=>simp only [D.pass,List.length_cons,ih];omega

theorem foldr_length (roots values : List K) : (roots.foldr D.pass values).length≤values.length := by
  induction roots with
  | nil=>rfl
  | cons root roots ih=>
    rw [List.foldr_cons,pass_length]
    omega

include hone hneg in
theorem factor_bound {R T : ℕ} (roots : List K) (target : K)
    (hr : ∀x∈roots,ArithmeticSize.Bound coeff R x) (ht : ArithmeticSize.Bound coeff T target) :
    ArithmeticSize.Bound coeff (roots.length*(T+R+2)) (D.factor roots target) := by
  induction roots with
  | nil=>simpa [D.factor] using (ArithmeticSize.Bound.one (coeff:=coeff))
  | cons root roots ih=>
    have one : ArithmeticSize.Bound coeff 0 (1:K):=ArithmeticSize.Bound.one
    have entry : ArithmeticSize.Bound coeff (T+R+2) (target-root) := by
      have hroot:=hr root (by simp)
      have hprod := hroot.mul one
      simpa only [Nat.add_zero,mul_one] using difference coeff unit neg hone hneg
        hroot (one.mono unit hone (by omega : 0≤T)) ht
    have rest:=ih (fun x hx=>hr x (by simp [hx]))
    have out:=entry.mul rest
    simpa only [D.factor,List.map_cons,List.prod_cons,List.length_cons,Nat.add_mul,Nat.one_mul,
      Nat.add_comm] using out


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PassBounds
end
