import Holant.Proofs.LinearProgramming.Optimization.Search.RegisterGrowth
import Holant.Proofs.LinearProgramming.Optimization.Search.SignedRound
import Holant.Proofs.LinearProgramming.Optimization.Search.InverseBounds

/-!
The actual signed storage operation on center AND factor, followed by an
explicit inflation. Small entry error is converted to nonsingularity,
inverse bounds and containment by finite rational linear algebra. No real
Neumann-series oracle, supplied inverse or correct-update premise is used.
These local quantitative lemmas feed RoundedTrajectory and RoundedTermination.
StepProgram and Complexity.CounterLoop provide the physical connection.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundedGeometry
open FactorUpdate Containment Projection
open scoped BigOperators Matrix
noncomputable section

def mass {n : ℕ} (x : Vec n) : ℚ := ∑ i, |x i|

theorem mass_nonneg {n : ℕ} (x : Vec n) : 0≤mass x :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (x i))

theorem coordinate_le_mass {n : ℕ} (x : Vec n) (i : Fin n) : |x i|≤mass x :=
  Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

theorem mass_eq_zero {n : ℕ} (x : Vec n) (h : mass x=0) : x=0 := by
  funext i
  have hi := coordinate_le_mass x i
  rw [h] at hi
  exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))

theorem action_bound {n : ℕ} (A : Mat n) (x : Vec n) (a : ℚ)
    (ha : 0≤a) (hA : ∀ i j, |A i j|≤a) (i : Fin n) :
    |(A.mulVec x) i|≤a*mass x := by
  calc
    _ ≤ ∑ j, |A i j*x j| := by
      simpa only [Matrix.mulVec,dotProduct] using Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, a*|x j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)
    _ = _ := by simp only [mass,Finset.mul_sum]

theorem mass_action {n : ℕ} (A : Mat n) (x : Vec n) (a : ℚ)
    (ha : 0≤a) (hA : ∀ i j, |A i j|≤a) :
    mass (A.mulVec x)≤(n:ℚ)*a*mass x := by
  calc
    _ ≤ ∑ _i : Fin n, a*mass x := Finset.sum_le_sum (fun i _ => action_bound A x a ha hA i)
    _ = _ := by simp; ring

def relative {n : ℕ} (A B : Mat n) : Mat n := A⁻¹*(B-A)

theorem relative_action {n : ℕ} (A B : Mat n) (hA : A.det≠0) (x : Vec n) :
    A⁻¹.mulVec (B.mulVec x)=x+(relative A B).mulVec x := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hb : B=A+(B-A) := by abel
  conv_lhs => rw [hb]
  rw [Matrix.add_mulVec,Matrix.mulVec_add,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hunit,Matrix.one_mulVec]
  rw [relative,Matrix.mulVec_mulVec]

/-- Any explicit entry perturbation satisfying n*delta≤1/2 is invertible.
The proof tests its actual kernel; no condition-number certificate is input. -/
theorem perturbed_nonsingular {n : ℕ} (A B : Mat n) (hA : A.det≠0)
    (delta : ℚ) (hd : 0≤delta) (hrel : ∀ i j, |relative A B i j|≤delta)
    (hsmall : (n:ℚ)*delta≤1/2) : B.det≠0 := by
  have hkernel : ∀ x : Vec n, B.mulVec x=0 → x=0 := by
    intro x hx
    have he := relative_action A B hA x
    rw [hx,Matrix.mulVec_zero] at he
    have hx' : x=-(relative A B).mulVec x := by
      funext i
      have hi := congrFun he i
      change 0=x i+((relative A B).mulVec x) i at hi
      change x i=-((relative A B).mulVec x) i
      linarith
    have hm : mass x≤(n:ℚ)*delta*mass x := by
      conv_lhs => rw [hx']
      simpa only [mass,Pi.neg_apply,abs_neg] using mass_action (relative A B) x delta hd hrel
    have hz : mass x=0 := by nlinarith [mass_nonneg x]
    exact mass_eq_zero x hz
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have hz : B.mulVec (x-y)=0 := by rw [Matrix.mulVec_sub,hxy,sub_self]
    exact sub_eq_zero.mp (hkernel _ hz)
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj))

/-- A perturbation costs at most a factor two in the previous inverse bound.
All occurrences of B⁻¹ are mathematical proof terms, not runtime operations. -/
theorem perturbed_inverse {n : ℕ} (A B : Mat n) (hA : A.det≠0)
    (M delta : ℚ) (hM : 0≤M) (hd : 0≤delta)
    (hAi : ∀ i j, |A⁻¹ i j|≤M) (hrel : ∀ i j, |relative A B i j|≤delta)
    (hsmall : (n:ℚ)*delta≤1/2) (i j : Fin n) : |B⁻¹ i j|≤2*M := by
  have hB := perturbed_nonsingular A B hA delta hd hrel hsmall
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  let u := B⁻¹.mulVec (Pi.single j 1)
  have hu : B.mulVec u=Pi.single j 1 := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hunit,Matrix.one_mulVec]
  have he := relative_action A B hA u
  rw [hu] at he
  rw [Matrix.mulVec_single_one] at he
  have hc : ∀ k, |u k|≤M+delta*mass u := by
    intro k
    have he' : u k=A⁻¹ k j-((relative A B).mulVec u) k := by
      have h := congrFun he k
      change A⁻¹ k j = u k+((relative A B).mulVec u) k at h
      linarith
    rw [he']
    exact (abs_sub _ _).trans (add_le_add (hAi k j) (action_bound _ u delta hd hrel k))
  have hm : mass u≤(n:ℚ)*M+(n:ℚ)*delta*mass u := by
    calc
      _ ≤ ∑ _k : Fin n, (M+delta*mass u) := by
        unfold mass
        exact Finset.sum_le_sum (fun k _ => hc k)
      _ = _ := by simp; ring
  have hm' : mass u≤2*(n:ℚ)*M := by
    nlinarith [mass_nonneg u,mul_le_mul_of_nonneg_right hsmall (mass_nonneg u)]
  have hb : |u i|≤2*M := by
    calc
      _ ≤ M+delta*mass u := hc i
      _ ≤ M+delta*(2*(n:ℚ)*M) :=
        add_le_add (le_refl M) (mul_le_mul_of_nonneg_left hm' hd)
      _ ≤ 2*M := by nlinarith [mul_le_mul_of_nonneg_right hsmall hM]
  simpa only [u,Matrix.mulVec,dotProduct_single,mul_one] using hb

theorem relative_entry_bound {n : ℕ} (A B : Mat n) (M eps : ℚ)
    (hM : 0≤M) (he : 0≤eps) (hAi : ∀ i j, |A⁻¹ i j|≤M)
    (hE : ∀ i j, |B i j-A i j|≤eps) (i j : Fin n) :
    |relative A B i j|≤(n:ℚ)*M*eps :=
  RegisterGrowth.matrix_product A⁻¹ (B-A) M eps hM he hAi hE i j

theorem square_near {n : ℕ} (hn : 1≤n) (y w : Vec n) (t eta : ℚ)
    (ht : 0≤t) (he : 0≤eta) (hy : square y≤1) (hw : ∀ i, |w i|≤t)
    (hsmall : (n:ℚ)*t≤eta) : square (y+w)≤(1+eta)^2 := by
  have hn' : (1:ℚ)≤n := by exact_mod_cast hn
  have hteta : t≤eta := by nlinarith
  have hsq : square w≤(n:ℚ)*t^2 := by
    calc
      _ ≤ ∑ _i : Fin n, t^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hw i
        nlinarith [sq_abs (w i),abs_nonneg (w i)]
      _ = _ := by simp
  have hdot : y ⬝ᵥ w≤(n:ℚ)*t := by
    calc
      _ ≤ |y ⬝ᵥ w| := le_abs_self _
      _ ≤ ∑ i, |y i*w i| := by simpa only [dotProduct] using Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, t := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul (InverseBounds.ball_coordinate y hy i)
          (hw i) (abs_nonneg _) (by norm_num : (0:ℚ)≤1)
      _ = _ := by simp
  have hsq' : (n:ℚ)*t^2≤eta^2 := by
    have h := mul_le_mul hsmall hteta ht he
    nlinarith
  have hid : y+w=(1:ℚ) • y+(1:ℚ) • w := by simp
  rw [hid,square_linear]
  nlinarith

def roundedMatrix {n : ℕ} (A : Mat n) (h : ℕ) : Mat n := fun i j => SignedRound.value (A i j,h)
def roundedCenter {n : ℕ} (c : Vec n) (h : ℕ) : Vec n := fun i => SignedRound.value (c i,h)
def value {n : ℕ} (s : State n) (h : ℕ) (eta : ℚ) : State n :=
  { center := roundedCenter s.center h
    factor := (1+eta) • roundedMatrix s.factor h }

theorem round_error {n : ℕ} (s : State n) (h : ℕ) (hh : 0<h) :
    (∀ i, |roundedCenter s.center h i-s.center i|≤1/(h:ℚ)) ∧
    (∀ i j, |roundedMatrix s.factor h i j-s.factor i j|≤1/(h:ℚ)) :=
  ⟨fun i => (SignedRound.error _ h hh).le,fun i j => (SignedRound.error _ h hh).le⟩

theorem round_inverse {n : ℕ} (s : State n) (h : ℕ) (hh : 0<h)
    (hR : s.factor.det≠0) (M : ℚ) (hM : 0≤M) (hi : ∀ i j, |s.factor⁻¹ i j|≤M)
    (hsmall : (n:ℚ)^2*M/(h:ℚ)≤1/2) :
    (roundedMatrix s.factor h).det≠0 ∧ ∀ i j, |(roundedMatrix s.factor h)⁻¹ i j|≤2*M := by
  have hd : (0:ℚ)≤(n:ℚ)*M*(1/(h:ℚ)) := by positivity
  have hr := relative_entry_bound s.factor (roundedMatrix s.factor h) M (1/(h:ℚ))
    hM (by positivity) hi (round_error s h hh).2
  have hs : (n:ℚ)*((n:ℚ)*M*(1/(h:ℚ)))≤1/2 := by
    have heq : (n:ℚ)*((n:ℚ)*M*(1/(h:ℚ)))=(n:ℚ)^2*M/(h:ℚ) := by ring
    rw [heq]
    exact hsmall
  exact ⟨perturbed_nonsingular _ _ hR _ hd hr hs,
    perturbed_inverse _ _ hR M _ hM hd hi hr hs⟩

/-- Center and matrix storage errors are BOTH charged. The input point need
only be contained by the old ellipsoid; it is not assumed feasible or deep.
-/
theorem contains {n : ℕ} (hn : 1≤n) (s : State n) (h : ℕ) (hh : 0<h)
    (eta M : ℚ) (he : 0≤eta) (hM : 0≤M) (hR : s.factor.det≠0)
    (hi : ∀ i j, |s.factor⁻¹ i j|≤M)
    (hsmall : (n:ℚ)^2*M/(h:ℚ)≤1/2)
    (hcover : 2*(n:ℚ)^2*((n:ℚ)+1)*M/(h:ℚ)≤eta)
    (x : Vec n) (hx : Contains s x) : Contains (value s h eta) x := by
  obtain ⟨y,hy,hxy⟩ := hx
  let B := roundedMatrix s.factor h
  let c := roundedCenter s.center h
  obtain ⟨hB,hBi⟩ := round_inverse s h hh hR M hM hi hsmall
  have hbunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  let u := B⁻¹.mulVec (x-c)
  let w := u-y
  have hwidentity : w=B⁻¹.mulVec ((s.center-c)+(s.factor-B).mulVec y) := by
    have hby : B⁻¹.mulVec (B.mulVec y)=y := by
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hbunit,Matrix.one_mulVec]
    rw [Matrix.mulVec_add,Matrix.sub_mulVec,Matrix.mulVec_sub,Matrix.mulVec_sub,hby]
    dsimp [w,u]
    rw [hxy,Matrix.mulVec_sub,Matrix.mulVec_add]
    abel
  have hdelta : ∀ i, |((s.center-c)+(s.factor-B).mulVec y) i|≤((n:ℚ)+1)/(h:ℚ) := by
    intro i
    have hc : |(s.center-c) i|≤1/(h:ℚ) := by
      simpa only [c,Pi.sub_apply,abs_sub_comm] using (round_error s h hh).1 i
    have hm : |((s.factor-B).mulVec y) i|≤(n:ℚ)/(h:ℚ) := by
      calc
        _ ≤ ∑ j, |(s.factor i j-B i j)*y j| := by
          simpa only [Matrix.mulVec,dotProduct,Matrix.sub_apply] using Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin n, 1/(h:ℚ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          have hE : |s.factor i j-B i j|≤1/(h:ℚ) := by
            simpa only [B,abs_sub_comm] using (round_error s h hh).2 i j
          simpa only [mul_one] using mul_le_mul hE (InverseBounds.ball_coordinate y hy j)
            (abs_nonneg _) (by positivity : (0:ℚ)≤1/(h:ℚ))
        _ = _ := by simp; ring
    apply (abs_add_le _ _).trans
    change |(s.center-c) i|+|((s.factor-B).mulVec y) i|≤_
    have heq : (1:ℚ)/(h:ℚ)+(n:ℚ)/(h:ℚ)=((n:ℚ)+1)/(h:ℚ) := by ring
    rw [←heq]
    exact add_le_add hc hm
  let t : ℚ := 2*(n:ℚ)*((n:ℚ)+1)*M/(h:ℚ)
  have hw : ∀ i, |w i|≤t := by
    intro i
    rw [hwidentity]
    calc
      _ ≤ (2*M)*mass ((s.center-c)+(s.factor-B).mulVec y) :=
        action_bound B⁻¹ _ (2*M) (by positivity) hBi i
      _ ≤ (2*M)*((n:ℚ)*(((n:ℚ)+1)/(h:ℚ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℚ)≤2*M)
        calc
          _ ≤ ∑ _i : Fin n, ((n:ℚ)+1)/(h:ℚ) := Finset.sum_le_sum (fun i _ => hdelta i)
          _ = _ := by simp
      _ = t := by dsimp [t]; ring
  have ht : (0:ℚ)≤t := by dsimp [t]; positivity
  have hs : square u≤(1+eta)^2 := by
    have hu : u=y+w := by dsimp [w]; abel
    rw [hu]
    apply square_near hn y w t eta ht he hy hw
    dsimp only [t]
    have heq : (n:ℚ)*(2*(n:ℚ)*((n:ℚ)+1)*M/(h:ℚ))=
        2*(n:ℚ)^2*((n:ℚ)+1)*M/(h:ℚ) := by ring
    rw [heq]
    exact hcover
  have hp : (0:ℚ)<1+eta := by linarith
  refine ⟨(1/(1+eta)) • u,?_,?_⟩
  · rw [square_smul]
    have hid : (1/(1+eta))^2*square u=square u/(1+eta)^2 := by
      rw [one_div,div_eq_mul_inv,←inv_pow,mul_comm]
    rw [hid]
    exact (div_le_one (sq_pos_of_pos hp)).mpr hs
  · change x=c+((1+eta) • B).mulVec ((1/(1+eta)) • u)
    rw [Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,
      mul_one_div_cancel (ne_of_gt hp),one_smul]
    dsimp only [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hbunit,Matrix.one_mulVec]
    abel

theorem nonsingular {n : ℕ} (s : State n) (h : ℕ) (hh : 0<h)
    (eta M : ℚ) (he : 0≤eta) (hM : 0≤M) (hR : s.factor.det≠0)
    (hi : ∀ i j, |s.factor⁻¹ i j|≤M) (hsmall : (n:ℚ)^2*M/(h:ℚ)≤1/2) :
    (value s h eta).factor.det≠0 := by
  have hb := (round_inverse s h hh hR M hM hi hsmall).1
  change ((1+eta) • roundedMatrix s.factor h).det≠0
  rw [Matrix.det_smul,Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero _ (by linarith : (1:ℚ)+eta≠0)) hb

theorem bounded {n : ℕ} (s : State n) (h : ℕ) (hh : 0<h)
    (eta M : ℚ) (he : 0≤eta) (he1 : eta≤1) (hM : 0≤M) (hR : s.factor.det≠0)
    (hs : RegisterGrowth.Bounded s M) (hsmall : (n:ℚ)^2*M/(h:ℚ)≤1/2) :
    RegisterGrowth.Bounded (value s h eta) (2*M) := by
  let B := roundedMatrix s.factor h
  have hp : (0:ℚ)<1+eta := by linarith
  have hb := round_inverse s h hh hR M hM hs.2.2 hsmall
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hb.1
  have hinv : ((1+eta) • B)⁻¹=(1/(1+eta)) • B⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      Matrix.mul_nonsing_inv _ hu,mul_one_div_cancel (ne_of_gt hp),one_smul]
  have hscalar : (1:ℚ)/(1+eta)≤1 := (div_le_one hp).mpr (by linarith)
  refine ⟨?_,?_,?_⟩
  · intro i
    exact ((SignedRound.magnitude (s.center i) h hh).trans (hs.1 i)).trans (by linarith)
  · intro i j
    change |(1+eta)*SignedRound.value (s.factor i j,h)|≤2*M
    rw [abs_mul,abs_of_pos hp]
    exact mul_le_mul (by linarith : (1:ℚ)+eta≤2)
      ((SignedRound.magnitude _ h hh).trans (hs.2.1 i j)) (abs_nonneg _) (by norm_num)
  · intro i j
    change |((1+eta) • B)⁻¹ i j|≤2*M
    rw [hinv]
    change |(1/(1+eta))*B⁻¹ i j|≤2*M
    rw [abs_mul,abs_of_pos (by positivity : (0:ℚ)<1/(1+eta))]
    simpa only [one_mul] using mul_le_mul hscalar (hb.2 i j) (abs_nonneg _) (by norm_num : (0:ℚ)≤1)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundedGeometry
