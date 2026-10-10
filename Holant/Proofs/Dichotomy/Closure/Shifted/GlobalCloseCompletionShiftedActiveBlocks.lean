import Holant.Marked.SupportAtlas.Source
import Holant.Projective.CyclicPhasePencil.Rigidity
import Holant.Certificates.EqualityQuaternary.CoordinatePrimality
import Holant.Tractable.Product

/-! Generic shifted-coset active-block algebra, separated from the old frozen-state wrapper.
A-coset active-block algebra from actual weighted samples. The affine pencil
relation is DERIVED. Two active blocks contradict a sampled crossing card;
one active block has an explicit ordered 2+2 factorization. No factorization
or desired endpoint is supplied as an input.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedActiveBlocks
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective
open Holant.Certificates.EqualityQuaternary
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option Elab.async false
namespace CQ
export Holant.Projective.CyclicQuaternary (Blocks ofCoordinates)
export Holant.Marked.SupportAtlas (ofCoordinates_atoms)
end CQ
namespace CP
export Holant.Projective.CyclicPhasePencil
  (diagonal diagonal_eq_zero_iff ScalarSample ScalarSamples relation_of_samples affine_zero)
end CP

def order (i : Fin 3) : Equiv.Perm (Fin 4) :=
  if i=0 then Equiv.refl _ else if i=1 then Equiv.swap 1 2
    else (Equiv.swap 1 3).trans (Equiv.swap 1 2)
def other (i j : Fin 3) (h : i<j) : Fin 3 := ⟨3-i.val-j.val,by
  have := i.isLt
  have := j.isLt
  change i.val<j.val at h
  omega⟩

theorem diagonal_sample (a h d t : ℂ) (xs : CQ.Blocks ℂ) (i : Fin 3) :
    weightedCard d (CQ.ofCoordinates a h xs) (order i) false t=
      CP.diagonal (a+d*t*(xs i).1) ((xs i).2+d*t*h) := by
  rw [weightedCard_even]
  have hzero : slice (CQ.ofCoordinates a h xs) (order i) false false =
      CP.diagonal a (xs i).2 := by
    fin_cases i <;> funext u v <;> cases u <;> cases v <;>
      simp [slice,fill_eq_join,join,order,CQ.ofCoordinates,CP.diagonal,
        Equiv.swap_apply_def,Equiv.trans_apply,Equiv.symm_trans_apply]
  have hone : slice (CQ.ofCoordinates a h xs) (order i) true false =
      CP.diagonal (xs i).1 h := by
    fin_cases i <;> funext u v <;> cases u <;> cases v <;>
      simp [slice,fill_eq_join,join,order,CQ.ofCoordinates,CP.diagonal,
        Equiv.swap_apply_def,Equiv.trans_apply,Equiv.symm_trans_apply]
  rw [hzero,hone]
  funext u v
  cases u <;> cases v <;> simp [binaryPencil,CP.diagonal,smul_eq_mul] <;> ring

def off (u v : ℂ) : CMat := fun a b => if a then (if b then 0 else v) else (if b then u else 0)
theorem crossing_sample (a h d t : ℂ) (xs : CQ.Blocks ℂ)
    (i j : Fin 3) (hij : i<j) :
    weightedCard d (CQ.ofCoordinates a h xs) (order (other i j hij)) true t=
      off (t*(xs i).2+d*(xs j).1) (t*(xs j).2+d*(xs i).1) := by
  funext u v
  fin_cases i <;> fin_cases j <;> try { norm_num at hij }
  all_goals cases u <;> cases v <;>
    simp [weightedCard,effectiveKernel,off,CQ.ofCoordinates,order,other,join,
      Equiv.swap_apply_def,Equiv.trans_apply,Equiv.symm_trans_apply] <;> ring

theorem diagonal_safe {m : ℕ} (d u v : ℂ) (hd : d≠0)
    (h : SafeWeighted m d (CP.diagonal u v)) : CP.ScalarSample m u (d*v) := by
  rcases h with hz|hh
  · have hz' := (CP.diagonal_eq_zero_iff u v).mp hz
    exact Or.inl ⟨hz'.1,by rw [hz'.2,mul_zero]⟩
  · right
    simpa [IsRootMonomial,Kernel.mul_apply,CP.diagonal,diagonalC,mul_comm] using hh

/-- All three alternatives of the existing root-pencil theorem are retained
until the actual endpoint/active hypotheses exclude the degenerate ones. -/
theorem active_relation {m : ℕ} (hm : 3≤m) (d a h x y : ℂ)
    (hd : d≠0) (ha : a≠0) (hx : x≠0)
    (hs : ∀t : ℂ,t^m=1 → SafeWeighted m d (CP.diagonal (a+d*t*x) (y+d*t*h))) :
    x*y=a*h ∧ (d*(y/a))^m=1 := by
  have samples : CP.ScalarSamples m a (-d*x) (-d*y) (d^2*h) := by
    intro t ht
    convert diagonal_safe d _ _ hd (hs t ht) using 1 <;> ring
  obtain ⟨r,hr,hp|hp|hp⟩ := CP.relation_of_samples hm _ _ _ _ samples
  · have hy : d*y=r*a := by linear_combination -hp.1
    have hh : d*h=r*x := by
      apply (mul_left_cancel₀ hd)
      linear_combination hp.2
    constructor
    · apply (mul_left_cancel₀ hd)
      calc
        d*(x*y)=x*(d*y) := by ring
        _ = a*(d*h) := by rw [hy,hh]; ring
        _ = d*(a*h) := by ring
    · have he : d*(y/a)=r := by rw [←mul_div_assoc,hy]; field_simp [ha]
      rwa [he]
  · exact ((mul_ne_zero (neg_ne_zero.mpr hd) hx) hp.1).elim
  · exact (ha hp.1).elim

theorem inactive_ratio {m : ℕ} (d a h : ℂ) (hd : d≠0) (ha : a≠0) (hh : h≠0)
    (hdroot : (d^2)^m=1)
    (hs : SafeWeighted m d (CP.diagonal a (d*h))) : (h/a)^m=1 := by
  have h := diagonal_safe d a (d*h) hd hs
  rcases h with hz|hn
  · exact (ha hz.1).elim
  · have he : d*(d*h)/a=d^2*(h/a) := by ring
    simpa [he,mul_pow,hdroot] using hn.2.2

theorem exists_affine_sample {m : ℕ} (hm : 3≤m) (a b : ℂ) (ha : a≠0) :
    ∃t : ℂ,t^m=1 ∧ t*a+b≠0 := by
  by_contra hn
  push_neg at hn
  have hh := CP.affine_zero hm b (-a) (by intro t ht; simpa [add_comm] using hn t ht)
  exact ha (neg_eq_zero.mp hh.2)

theorem off_root_ratio_unsafe {m : ℕ} (d u v : ℂ) (hd : d≠0) (hnot : d^m≠1)
    (hu : u≠0) (hv : v≠0) (hr : (v/u)^m=1) : ¬SafeWeighted m d (off u v) := by
  rintro (hz|hm)
  · exact hu (congrFun (congrFun hz false) true)
  · have hh : (v/(u*d))^m=1 := by
      simpa [IsRootMonomial,off,Kernel.mul_apply,diagonalC,hu,hv,hd] using hm
    have he : v/(u*d)=(v/u)/d := by field_simp [hu,hd]
    rw [he,div_pow,hr] at hh
    exact hnot (((div_eq_one_iff_eq (pow_ne_zero _ hd)).mp hh |>.symm))

/-- A concrete root sample witnesses the unsafe crossing. In the unchanged
branch its safety is already proved, so no fake progress event is returned. -/
theorem two_active_unsafe {m : ℕ} (hm : 3≤m) (d a h x y z w : ℂ)
    (hd : d≠0) (hnot : d^m≠1) (ha : a≠0) (hy : y≠0) (hw : w≠0)
    (hxy : x*y=a*h) (hzw : z*w=a*h)
    (hry : (d*(y/a))^m=1) (hrw : (d*(w/a))^m=1) :
    ∃t : ℂ,t^m=1 ∧ ¬SafeWeighted m d (off (t*y+d*z) (t*w+d*x)) := by
  obtain ⟨t,ht,hu⟩ := exists_affine_sample hm y (d*z) hy
  have hvEq : t*w+d*x=(w/y)*(t*y+d*z) := by
    field_simp [hy]
    linear_combination d*(hxy-hzw)
  have hratio : (w/y)^m=1 := by
    have he : w/y=(d*(w/a))/(d*(y/a)) := by field_simp [hd,ha,hy]
    rw [he,div_pow,hrw,hry,div_one]
  refine ⟨t,ht,off_root_ratio_unsafe d _ _ hd hnot hu ?_ ?_⟩
  · rw [hvEq]
    exact mul_ne_zero (div_ne_zero hw hy) hu
  · rw [hvEq,mul_div_cancel_right₀ _ hu]
    exact hratio

theorem at_most_one {m : ℕ} (hm : 3≤m) (d a h : ℂ) (xs : CQ.Blocks ℂ)
    (hd : d≠0) (hnot : d^m≠1) (ha : a≠0)
    (paired : ∀i,(xs i).1=0 ↔ (xs i).2=0)
    (deck : SafeDeck m d (CQ.ofCoordinates a h xs)) :
    ∀i j,(xs i).1≠0 → (xs j).1≠0 → i=j := by
  have ordered (i j : Fin 3) (hij : i<j) (hi : (xs i).1≠0) (hj : (xs j).1≠0) : False := by
    have hi' := active_relation hm d a h _ _ hd ha hi
      (fun t ht => diagonal_sample a h d t xs i ▸ deck (order i) false t ht)
    have hj' := active_relation hm d a h _ _ hd ha hj
      (fun t ht => diagonal_sample a h d t xs j ▸ deck (order j) false t ht)
    obtain ⟨t,ht,hu⟩ := two_active_unsafe hm d a h _ _ _ _ hd hnot ha
      ((paired i).not.mp hi) ((paired j).not.mp hj) hi'.1 hj'.1 hi'.2 hj'.2
    exact hu (crossing_sample a h d t xs i j hij ▸ deck (order (other i j hij)) true t ht)
  intro i j hi hj
  rcases lt_trichotomy i j with hij|hij|hij
  · exact (ordered i j hij hi hj).elim
  · exact hij
  · exact (ordered j i hij hj hi).elim

def blocks (K : Finset (Fin 3)) (b c : Fin 3 → Scalar) : CQ.Blocks Scalar :=
  fun i => if i∈K then (b i,c i) else (0,0)
theorem complement_coordinates (a h : Scalar) (K : Finset (Fin 3)) (b c : Fin 3 → Scalar) :
    complementExpression a h K b c=CQ.ofCoordinates a h (blocks K b c) := by
  rw [CQ.ofCoordinates_atoms]
  unfold complementExpression blocks
  congr 1
  symm
  calc
    _ = ∑ i ∈ K, ((if i∈K then (b i,c i) else (0,0)).1 • atom (pairWord i) +
        (if i∈K then (b i,c i) else (0,0)).2 • atom (complement (pairWord i))) := by
      apply Eq.symm
      apply Finset.sum_subset (Finset.subset_univ K)
      intro i _ hi
      simp [hi]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]

/-- The singleton branch has literal diagonal factors and explicit ports. -/
theorem singleton_factor (a h : Scalar) (xs : CQ.Blocks Scalar) (i : Fin 3)
    (ha : a≠0) (hprod : (xs i).1*(xs i).2=a*h)
    (hother : ∀j,j≠i → xs j=(0,0)) :
    ProperFactor (CQ.ofCoordinates a h xs) := by
  refine ⟨2,2,by decide,by decide,finSumFinEquiv.trans (order i),
    kernelSignature (diagonalKernel a (xs i).1),
    kernelSignature (diagonalKernel 1 ((xs i).2/a)),?_⟩
  have hh : (xs i).1*((xs i).2/a)=h := by
    rw [←mul_div_assoc,hprod,mul_div_cancel_left₀ _ ha]
  funext w
  have hw : w=![w 0,w 1,w 2,w 3] := by funext j; fin_cases j <;> rfl
  rw [hw]
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with rfl | rfl | rfl <;> cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [CQ.ofCoordinates,Tensor.reindex,Tensor.tensor,kernelSignature,diagonalKernel,
      order,finSumFinEquiv,Equiv.trans_apply,Equiv.swap_apply_def,hother,hh,ha] <;>
      field_simp [ha] <;> linear_combination -hprod

/-- The complete A-coset classification on a PRIME atlas table. No active
block survives: two violate an actual sample, one gives the displayed cut. -/
theorem prime_is_equality {m : ℕ} (hm : 3≤m) (d : ℂ) (hd : d≠0)
    (hdroot : (d^2)^m=1) (hnot : d^m≠1) (g : Signature Scalar 4)
    (hc : ComplementForm g) (hp : TensorPrime g)
    (deck : SafeDeck m d (complexTensor g)) :
    ∃a h : Scalar,a≠0 ∧ h≠0 ∧ Roots m (h/a) ∧
      g=CQ.ofCoordinates a h (fun _ => (0,0)) := by
  obtain ⟨a,h,K,b,c,ha,hh,hb,hc,hg⟩ := hc
  let xs := blocks K b c
  have he : g=CQ.ofCoordinates a h xs := hg.trans (complement_coordinates a h K b c)
  let ys : CQ.Blocks ℂ := fun i => ((xs i).1,(xs i).2)
  have hmap : complexTensor g=CQ.ofCoordinates (a:ℂ) (h:ℂ) ys := by
    rw [he]
    funext w
    cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
      simp [complexTensor,CQ.ofCoordinates,ys,h0,h1,h2,h3]
  have hdeck : SafeDeck m d (CQ.ofCoordinates (a:ℂ) (h:ℂ) ys) := hmap ▸ deck
  have paired : ∀i,(ys i).1=0 ↔ (ys i).2=0 := by
    intro i
    by_cases hi : i∈K
    · simp [ys,xs,blocks,hi,hb i hi,hc i hi]
    · simp [ys,xs,blocks,hi]
  have unique := at_most_one hm d (a:ℂ) (h:ℂ) ys hd hnot (by exact_mod_cast ha) paired hdeck
  have zero_first (i : Fin 3) : (ys i).1=0 ↔ (xs i).1=0 := by simp [ys]
  have zero_second (i : Fin 3) : (ys i).2=0 ↔ (xs i).2=0 := by simp [ys]
  have hz : ∀i,xs i=(0,0) := by
    intro i
    by_cases hi : (xs i).1=0
    · have hiC : (ys i).1=0 := (zero_first i).mpr hi
      have hi' : (xs i).2=0 := (zero_second i).mp ((paired i).mp hiC)
      exact Prod.ext hi hi'
    · have hprod := (active_relation hm d (a:ℂ) (h:ℂ) (ys i).1 (ys i).2
        hd (by exact_mod_cast ha) ((zero_first i).not.mpr hi)
        (fun t ht => diagonal_sample _ _ _ _ _ _ ▸ hdeck (order i) false t ht)).1
      have ho : ∀j,j≠i → xs j=(0,0) := by
        intro j hji
        have hzj : (ys j).1=0 := by
          by_contra hj
          exact hji (unique j i hj ((zero_first i).not.mpr hi))
        exact Prod.ext ((zero_first j).mp hzj) ((zero_second j).mp ((paired j).mp hzj))
      dsimp only [ys] at hprod
      exact (hp.2 (he.symm ▸ singleton_factor a h xs i ha (by exact_mod_cast hprod) ho)).elim
  have hx : xs=(fun _ => (0,0)) := funext hz
  have hsamp := hdeck (order 0) false 1 (by simp)
  rw [diagonal_sample] at hsamp
  have hz0 := hz 0
  have hy0 : ys 0=(0,0) := by simp [ys,hz0]
  simp only [hy0,mul_zero,add_zero,zero_add,mul_one] at hsamp
  have hr := inactive_ratio d (a:ℂ) (h:ℂ) hd (by exact_mod_cast ha)
    (by exact_mod_cast hh) hdroot hsamp
  exact ⟨a,h,ha,hh,by exact_mod_cast hr,by rw [he,hx]⟩

set_option maxHeartbeats 2000000 in
/-- An explicit product formula after undoing the atlas mask. The three
constraints retain the original ordered ports; no closure premise is used. -/
theorem flipped_equality_product (a h : Scalar) (ha : a≠0) (mask : Word) :
    Product (Flip.value (CQ.ofCoordinates a h (fun _ => (0,0))) mask) := by
  let u : Bool → Scalar := fun b => if b ^^ mask 0 then h else a
  have hu : u≠0 := by
    intro hz
    have hv := congrFun hz (mask 0)
    exact ha (by simpa [u] using hv)
  let edge : Fin 4 → ProductFactor 4 := fun j =>
    if mask 0=mask j then .equality 0 j else .disequality 0 j
  have he : Flip.value (CQ.ofCoordinates a h (fun _ => (0,0))) mask=
      productFormula 1 [.unary 0 u hu,edge 1,edge 2,edge 3] := by
    funext x
    cases h0 : mask 0 <;> cases h1 : mask 1 <;>
      cases h2 : mask 2 <;> cases h3 : mask 3 <;>
      cases x0 : x 0 <;> cases x1 : x 1 <;> cases x2 : x 2 <;> cases x3 : x 3 <;>
      simp [Flip.value,xorWord,CQ.ofCoordinates,productFormula,ProductFactor.eval,
        edge,u,Signature.equality,Signature.disequality,h0,h1,h2,h3,x0,x1,x2,x3]
  rw [he]
  exact product_formula _ _


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedActiveBlocks
