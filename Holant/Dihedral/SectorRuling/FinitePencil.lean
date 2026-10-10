import Holant.Dihedral.SectorRuling.CubeRatio

/-! Common support is derived from all finite phase samples. The m=3 branch
uses the negative cube-root ratio obstruction; m>=4 uses two forced zeros of
one literal affine entry. Zero samples are allowed in the input. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant.Marked
variable {X J : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X] [DecidableEq X]
  [Fintype J] [DecidableEq J]

def pencil (U V : X → Scalar) (t : Scalar) : X → Scalar := fun x => U x+t*V x

theorem interpolate_pencil (U V : X → Scalar) (a b t : Scalar) (hab : a ≠ b) :
    pencil U V t=combination ((b-t)/(b-a)) ((t-a)/(b-a)) (pencil U V a) (pencil U V b) := by
  funext x
  simp only [pencil,combination]
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

def SampleInfo (m N : ℕ) (f : X → Scalar) : Prop :=
  AffineClosed (support f) ∧ (support f).card=N ∧
    ∀ x y,f x ≠ 0 → f y ≠ 0 → Roots m (f x/f y)

private theorem exclusive_word (S T : Finset X) (hc : S.card=T.card) (hne : S ≠ T) :
    ∃ x,x ∈ S ∧ x ∉ T := by
  by_contra hn
  push_neg at hn
  exact hne (Finset.eq_of_subset_of_card_le hn (by omega))

private theorem third_index (i j : J) (hc : 2<Fintype.card J) : ∃ k : J,k ≠ i ∧ k ≠ j := by
  classical
  have h : ({i,j} : Finset J).card < (Finset.univ : Finset J).card := by
    have hh := Finset.card_insert_le i ({j} : Finset J)
    simp only [Finset.card_singleton,Finset.card_univ] at hh ⊢
    omega
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨k,by simpa using hk⟩

private theorem fourth_index (i j k : J) (hc : 3<Fintype.card J) :
    ∃ l : J,l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  classical
  have h : ({i,j,k} : Finset J).card < (Finset.univ : Finset J).card := by
    have h₀ := Finset.card_insert_le i ({j,k} : Finset J)
    have h₁ := Finset.card_insert_le j ({k} : Finset J)
    simp only [Finset.card_singleton,Finset.card_univ] at h₀ h₁ ⊢
    omega
  obtain ⟨l,_,hl⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨l,by simpa using hl⟩

/-- Exact finite-sample support rigidity. The support/ratio inputs are later
proved from the actual current-group matching coefficient products. -/
theorem finite_pencil_support {m N : ℕ} (hm : 3 ≤ m) (hN : 0<N)
    (τ : J → Scalar) (hτ : Function.Injective τ) (hcard : Fintype.card J=m)
    (U V : X → Scalar) (hs : ∀ j,pencil U V (τ j)=0 ∨ SampleInfo m N (pencil U V (τ j)))
    (i j : J) (hi : pencil U V (τ i) ≠ 0) (hj : pencil U V (τ j) ≠ 0) :
    support (pencil U V (τ i))=support (pencil U V (τ j)) := by
  classical
  obtain ⟨hAi,hNi,hRi⟩ := (hs i).resolve_left hi
  obtain ⟨hAj,hNj,hRj⟩ := (hs j).resolve_left hj
  by_contra hne
  have hij : i ≠ j := by intro he; subst j; exact hne rfl
  have hτij : τ i ≠ τ j := fun h => hij (hτ h)
  let A := pencil U V (τ i)
  let B := pencil U V (τ j)
  let c₀ := fun k => (τ j-τ k)/(τ j-τ i)
  let c₁ := fun k => (τ k-τ i)/(τ j-τ i)
  have hcomb (k : J) : pencil U V (τ k)=combination (c₀ k) (c₁ k) A B :=
    interpolate_pencil U V (τ i) (τ j) (τ k) hτij
  have hhalf : 2*(support A∩support B).card ≤ N := by
    rw [←hNi]
    exact affine_intersection_half _ _ hAi hAj (hNi.trans hNj.symm) hne
  obtain ⟨x,hxA,hxB⟩ := exclusive_word (support A) (support B) (hNi.trans hNj.symm) hne
  obtain ⟨y,hyB,hyA⟩ := exclusive_word (support B) (support A) (hNj.trans hNi.symm) (Ne.symm hne)
  have hxA' : A x ≠ 0 := (mem_support _ _).mp hxA
  have hxB' : B x=0 := by simpa using hxB
  have hyB' : B y ≠ 0 := (mem_support _ _).mp hyB
  have hyA' : A y=0 := by simpa using hyA
  have third (k : J) (hki : k ≠ i) (hkj : k ≠ j) :
      c₀ k ≠ 0 ∧ c₁ k ≠ 0 ∧ SampleInfo m N (pencil U V (τ k)) ∧
      (support A∩support B).Nonempty ∧ ∀ w ∈ support A∩support B,pencil U V (τ k) w=0 := by
    have hc₀ : c₀ k ≠ 0 := div_ne_zero (sub_ne_zero.mpr (fun he => hkj (hτ he.symm))) (sub_ne_zero.mpr hτij.symm)
    have hc₁ : c₁ k ≠ 0 := div_ne_zero (sub_ne_zero.mpr (fun he => hki (hτ he))) (sub_ne_zero.mpr hτij.symm)
    have hn : pencil U V (τ k) ≠ 0 := by
      intro hz
      have hh := congrFun hz x
      rw [hcomb] at hh
      simp only [combination,hxB',mul_zero,add_zero,Pi.zero_apply] at hh
      exact mul_ne_zero hc₀ hxA' hh
    have hk := (hs k).resolve_left hn
    have hc := third_support_cancellation (c₀ k) (c₁ k) hc₀ hc₁ A B N hN hNi hNj
      (by rw [←hcomb]; exact hk.2.1) hhalf
    exact ⟨hc₀,hc₁,hk,hc.2.2.1,fun w hw => by rw [hcomb]; exact hc.2.2.2 w hw⟩
  obtain ⟨k,hki,hkj⟩ := third_index i j (by omega)
  obtain ⟨hc₀,hc₁,hk,hI,hzero⟩ := third k hki hkj
  obtain ⟨w,hw⟩ := hI
  have hwA : A w ≠ 0 := (mem_support _ _).mp (Finset.mem_inter.mp hw).1
  have hwB : B w ≠ 0 := (mem_support _ _).mp (Finset.mem_inter.mp hw).2
  by_cases hm3 : m=3
  · have hz : c₀ k*A w+c₁ k*B w=0 := by
      have hh := hzero w hw
      rw [hcomb] at hh
      exact hh
    have hx : pencil U V (τ k) x=c₀ k*A x := by rw [hcomb]; simp only [combination,hxB',mul_zero,add_zero]
    have hy : pencil U V (τ k) y=c₁ k*B y := by rw [hcomb]; simp only [combination,hyA',mul_zero,zero_add]
    have hratio := hk.2.2 x y (by rw [hx]; exact mul_ne_zero hc₀ hxA') (by rw [hy]; exact mul_ne_zero hc₁ hyB')
    rw [hx,hy,hm3] at hratio
    exact cube_ratio_obstruction (c₀ k) (c₁ k) (A x) (A w) (B w) (B y) hc₁ hwA hyB' hz
      (by simpa only [hm3] using hRi x w hxA' hwA) (by simpa only [hm3] using hRj w y hwB hyB') hratio
  · obtain ⟨l,hli,hlj,hlk⟩ := fourth_index i j k (by omega)
    have hz₀ := hzero w hw
    have hz₁ := (third l hli hlj).2.2.2.2 w hw
    change U w+τ k*V w=0 at hz₀
    change U w+τ l*V w=0 at hz₁
    have hv : (τ k-τ l)*V w=0 := by linear_combination hz₀-hz₁
    have hτkl : τ k ≠ τ l := fun he => hlk (hτ he).symm
    have hv0 : V w=0 := (mul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr hτkl)
    have hu0 : U w=0 := by simpa [hv0] using hz₀
    exact hwA (by simp [A,pencil,hu0,hv0])

end Holant.Dihedral.SectorRuling
