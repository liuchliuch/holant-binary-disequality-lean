import Holant.Tractable.AffinePhaseCriterion
import Holant.ReedMuller.AffinePatching.AffineSupport

/-! Structural finite coverage of all Boolean linear spaces and affine cosets.
The recursion splits the first original coordinate; no supplied support list
or finite-atlas completeness premise is assumed. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
set_option backward.isDefEq.respectTransparency false

 def LinearClosed {n : ℕ} (S : Finset (Word n)) : Prop :=
  origin n∈S ∧ ∀x∈S,∀y∈S,xor x y∈S
 def TernaryClosed {n : ℕ} (S : Finset (Word n)) : Prop :=
  ∀x∈S,∀y∈S,∀z∈S,xor (xor x y) z∈S

 def liftFalse {n : ℕ} (S : Finset (Word n)) : Finset (Word (n+1)) :=
  S.image (Fin.cons false)
 def extendSpace {n : ℕ} (S : Finset (Word n)) (v : Word n) : Finset (Word (n+1)) :=
  liftFalse S ∪ S.image (fun x => Fin.cons true (xor v x))

 def linearCatalog : (n : ℕ) → Finset (Finset (Word n))
  | 0 => {{origin 0}}
  | n+1 => (linearCatalog n).image liftFalse ∪
      (linearCatalog n).biUnion (fun S => Finset.univ.image (extendSpace S))

 def translateSet {n : ℕ} (v : Word n) (S : Finset (Word n)) : Finset (Word n) :=
  S.image (xor v)
 def affineCatalog (n : ℕ) : Finset (Finset (Word n)) :=
  (linearCatalog n).biUnion (fun S => Finset.univ.image (fun v => translateSet v S))

 theorem cons_xor {n : ℕ} (a b : Bool) (x y : Word n) :
    xor (Fin.cons a x) (Fin.cons b y)=Fin.cons (a ^^ b) (xor x y) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · rfl

 theorem cons_origin (n : ℕ) : Fin.cons false (origin n)=origin (n+1) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

 @[simp] theorem false_mem_lift {n : ℕ} (S : Finset (Word n)) (x : Word n) :
    Fin.cons false x∈liftFalse S ↔ x∈S := by
  simp [liftFalse,Fin.cons_inj]
 @[simp] theorem true_not_mem_lift {n : ℕ} (S : Finset (Word n)) (x : Word n) :
    Fin.cons true x∉liftFalse S := by simp [liftFalse,Fin.cons_inj]

 @[simp] theorem false_mem_extend {n : ℕ} (S : Finset (Word n)) (v x : Word n) :
    Fin.cons false x∈extendSpace S v ↔ x∈S := by
  simp [extendSpace,Fin.cons_inj]

 @[simp] theorem true_mem_extend {n : ℕ} (S : Finset (Word n)) (v x : Word n) :
    Fin.cons true x∈extendSpace S v ↔ xor v x∈S := by
  simp only [extendSpace,Finset.mem_union,true_not_mem_lift,false_or,Finset.mem_image,Fin.cons_inj,true_and]
  constructor
  · rintro ⟨y,hy,h⟩
    have he := congrArg (xor v) h
    simp only [xor_cancel_left] at he
    exact he ▸ hy
  · intro h
    exact ⟨xor v x,h,xor_cancel_left v x⟩

 def zeroSection {n : ℕ} (S : Finset (Word (n+1))) : Finset (Word n) :=
  Finset.univ.filter (fun x => Fin.cons false x∈S)

 @[simp] theorem mem_zeroSection {n : ℕ} (S : Finset (Word (n+1))) (x : Word n) :
    x∈zeroSection S ↔ Fin.cons false x∈S := by simp [zeroSection]

 theorem zeroSection_linear {n : ℕ} (S : Finset (Word (n+1))) (hS : LinearClosed S) :
    LinearClosed (zeroSection S) := by
  refine ⟨?_,?_⟩
  · rw [mem_zeroSection,cons_origin]
    exact hS.1
  · intro x hx y hy
    rw [mem_zeroSection] at hx hy ⊢
    have h := hS.2 _ hx _ hy
    simpa only [cons_xor,Bool.false_xor] using h

 theorem linear_split {n : ℕ} (S : Finset (Word (n+1))) (hS : LinearClosed S) :
    S=liftFalse (zeroSection S) ∨ ∃v : Word n,S=extendSpace (zeroSection S) v := by
  by_cases hex : ∃v : Word n,Fin.cons true v∈S
  · obtain ⟨v,hv⟩ := hex
    right
    refine ⟨v,?_⟩
    ext x
    have hx : x=Fin.cons (x 0) (fun i : Fin n => x i.succ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [hx]
    generalize x 0=a
    generalize (fun i : Fin n => x i.succ)=y
    cases a
    · simp
    · rw [true_mem_extend,mem_zeroSection]
      constructor
      · intro hy
        simpa [cons_xor] using hS.2 _ hv _ hy
      · intro hy
        simpa [cons_xor] using hS.2 _ hv _ hy
  · left
    ext x
    have hx : x=Fin.cons (x 0) (fun i : Fin n => x i.succ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [hx]
    generalize x 0=a
    generalize (fun i : Fin n => x i.succ)=y
    cases a
    · simp
    · simp only [true_not_mem_lift,iff_false]
      intro h
      exact hex ⟨y,h⟩

/-- Every actual Boolean linear space occurs in the recursively generated
finite family, at arbitrary arity. -/
 theorem linearCatalog_complete (n : ℕ) (S : Finset (Word n)) (hS : LinearClosed S) :
    S∈linearCatalog n := by
  induction n with
  | zero =>
    have he : S={origin 0} := by
      ext x
      have hx : x=origin 0 := by funext i; exact Fin.elim0 i
      subst x
      simp [hS.1]
    simp [linearCatalog,he]
  | succ n ih =>
    have hL := ih (zeroSection S) (zeroSection_linear S hS)
    rcases linear_split S hS with he|⟨v,he⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨zeroSection S,hL,he.symm⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨zeroSection S,hL,
        Finset.mem_image.mpr ⟨v,Finset.mem_univ _,he.symm⟩⟩

 theorem translated_linear {n : ℕ} (S : Finset (Word n)) (hS : TernaryClosed S)
    (v : Word n) (hv : v∈S) : LinearClosed (translateSet v S) := by
  refine ⟨Finset.mem_image.mpr ⟨v,hv,xor_self v⟩,?_⟩
  rintro x hx y hy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨xor (xor a b) v,hS a ha b hb v hv,?_⟩
  funext i
  simp only [xor_apply]
  cases v i <;> cases a i <;> cases b i <;> rfl

 theorem translateSet_twice {n : ℕ} (v : Word n) (S : Finset (Word n)) :
    translateSet v (translateSet v S)=S := by
  simp [translateSet,Finset.image_image,Function.comp_def]

/-- Every nonempty genuine affine Boolean support is covered, without a
finite support-certificate hypothesis. -/
 theorem affineCatalog_complete {n : ℕ} (S : Finset (Word n)) (hne : S.Nonempty)
    (hS : TernaryClosed S) : S∈affineCatalog n := by
  obtain ⟨v,hv⟩ := hne
  exact Finset.mem_biUnion.mpr ⟨translateSet v S,
    linearCatalog_complete n _ (translated_linear S hS v hv),
    Finset.mem_image.mpr ⟨v,Finset.mem_univ _,translateSet_twice v S⟩⟩

 theorem affine_support_catalog {n : ℕ} (f : Signature AlgebraicComplex n) (hf : Affine f)
    (hn : f≠0) : (Finset.univ.filter (fun x => f x≠0))∈affineCatalog n := by
  classical
  have he : ∃x,f x≠0 := Function.ne_iff.mp hn
  apply affineCatalog_complete
  · obtain ⟨x,hx⟩ := he
    exact ⟨x,by simp [hx]⟩
  · intro x hx y hy z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ReedMuller.AffinePatching.affine_support_ternary f hf x y z
        (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2⟩

end Holant.Certificates.AffineEndpoint
