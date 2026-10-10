import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralModels

/-! The four actual octahedral dictionaries are forced by the two literal
physical Pauli marks. Similarities in this proof are group coordinates only. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Coordinates.Alignment
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.OctahedralSeparator
open Holant.Certificates.RainbowOrbit

def PairType (f : Form) (a b : S4) : Prop :=
  if f=0 then DoubleTransposition a ∧ DoubleTransposition b
  else if f=1 then Transposition a ∧ Transposition b
  else if f=2 then DoubleTransposition a ∧ Transposition b
  else Transposition a ∧ DoubleTransposition b

/-- The finite table uses the existing cycleType equality deciders for
both marks, together with the constructive Fin 4/if/and instances. -/
instance instDecidablePairType (f : Form) (a b : S4) : Decidable (PairType f a b) := by
  unfold PairType
  infer_instance

def involutionIndex : Fin 9 → Fin 24 := ![1,2,3,18,19,20,21,22,23]
theorem involution_index (i : Fin 24) (hi : Involution (fourPermutation i)) :
    ∃ t : Fin 9, i = involutionIndex t := by
  revert hi
  fin_cases i <;> decide +kernel

/-- Compute semiconjugacy in the literal finite permutation group by its
existing finite-function equality, without an arbitrary Prop decider. -/
local instance instDecidableSemiconjByS4 (a x y : S4) : Decidable (SemiconjBy a x y) :=
  inferInstanceAs (Decidable (a*x=y*a))

local instance instDecidableCommuteS4 (a b : S4) : Decidable (Commute a b) :=
  inferInstanceAs (Decidable (SemiconjBy a b b))

/-- An exact finite S4 calculation, including commuting and distinctness.
Reference pairs are (1,3)/(18,19)/(1,23)/(19,3). -/
theorem finite_pair (f : Form) (i j : Fin 24)
    (hi : Involution (fourPermutation i)) (hj : Involution (fourPermutation j))
    (ht : PairType f (fourPermutation i) (fourPermutation j))
    (hc : Commute (fourPermutation i) (fourPermutation j)) (hne : i ≠ j) :
    ∃ k : Fin 24,
      fourPermutation k * fourPermutation i * (fourPermutation k)⁻¹ =
        fourPermutation (Models.xIndex f) ∧
      fourPermutation k * fourPermutation j * (fourPermutation k)⁻¹ =
        fourPermutation (Models.zIndex f) := by
  obtain ⟨a,rfl⟩ := involution_index i hi
  obtain ⟨b,rfl⟩ := involution_index j hj
  have table : ∀ f : Form, ∀ a b : Fin 9,
      PairType f (fourPermutation (involutionIndex a)) (fourPermutation (involutionIndex b)) →
      Commute (fourPermutation (involutionIndex a)) (fourPermutation (involutionIndex b)) →
      involutionIndex a ≠ involutionIndex b → ∃ k : Fin 24,
        fourPermutation k*fourPermutation (involutionIndex a)*(fourPermutation k)⁻¹ =
          fourPermutation (Models.xIndex f) ∧
        fourPermutation k*fourPermutation (involutionIndex b)*(fourPermutation k)⁻¹ =
          fourPermutation (Models.zIndex f) := by
    intro f a b
    fin_cases f <;> fin_cases a <;> fin_cases b <;> decide +kernel
  exact table f a b ht hc hne

theorem literal_pair (f : Form) (x j : modelPGL .octahedral)
    (hx : Involution (octahedral_iso_S4 x)) (hj : Involution (octahedral_iso_S4 j))
    (ht : PairType f (octahedral_iso_S4 x) (octahedral_iso_S4 j))
    (hc : Commute x j) (hne : x ≠ j) :
    ∃ c : modelPGL .octahedral,
      c*x*c⁻¹ = indexedPGL .octahedral (Models.xIndex f) ∧
      c*j*c⁻¹ = indexedPGL .octahedral (Models.zIndex f) := by
  obtain ⟨i,rfl⟩ := indexedPGL_surjective .octahedral x
  obtain ⟨j,rfl⟩ := indexedPGL_surjective .octahedral j
  have hc' := hc.map octahedral_iso_S4.toMonoidHom
  have hc'' : Commute (fourPermutation i) (fourPermutation j) := by
    apply (commute_iff_eq _ _).mpr
    have he := hc'.eq
    change octahedral_iso_S4 (indexedPGL .octahedral i) *
      octahedral_iso_S4 (indexedPGL .octahedral j) =
      octahedral_iso_S4 (indexedPGL .octahedral j) *
      octahedral_iso_S4 (indexedPGL .octahedral i) at he
    simpa only [octahedral_iso_indexed] using he
  simp only [octahedral_iso_indexed] at hx hj ht
  obtain ⟨k,ha,hb⟩ := finite_pair f i j hx hj ht hc''
    (fun he => hne (congrArg (indexedPGL .octahedral) he))
  refine ⟨indexedPGL .octahedral k,?_,?_⟩ <;> apply octahedral_iso_S4.injective
  · simpa only [map_mul,map_inv,octahedral_iso_indexed] using ha
  · simpa only [map_mul,map_inv,octahedral_iso_indexed] using hb

theorem map_conj_mul (H : Subgroup (PGL2 ℂ)) (g h : PGL2 ℂ) :
    H.map (MulAut.conj (g*h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext q
  change (g*h)*q*(g*h)⁻¹ = g*(h*q*h⁻¹)*g⁻¹
  group


theorem pair_type_exists (a b : S4) (ha : Involution a) (hb : Involution b) :
    ∃ f : Form, PairType f a b := by
  by_cases hda : DoubleTransposition a
  · by_cases hdb : DoubleTransposition b
    · exact ⟨0,by simpa [PairType] using And.intro hda hdb⟩
    · exact ⟨2,by simpa [PairType] using (And.intro hda (((s4_involution_types b).mp hb).resolve_right hdb))⟩
  · have hta := ((s4_involution_types a).mp ha).resolve_right hda
    by_cases hdb : DoubleTransposition b
    · exact ⟨3,by simpa [PairType] using And.intro hta hdb⟩
    · exact ⟨1,by simpa [PairType] using (And.intro hta (((s4_involution_types b).mp hb).resolve_right hdb))⟩

private theorem conj_involution (g q : PGL2 ℂ)
    (hs : q*q=1) (hn : q≠1) (mem : g*q*g⁻¹∈modelPGL .octahedral) :
    Involution (octahedral_iso_S4 ⟨g*q*g⁻¹,mem⟩) := by
  let x : modelPGL .octahedral := ⟨g*q*g⁻¹,mem⟩
  have hx : x*x=1 := by
    apply Subtype.ext
    change (g*q*g⁻¹)*(g*q*g⁻¹)=1
    calc
      _ = g*(q*q)*g⁻¹ := by group
      _ = 1 := by rw [hs]; group
  refine ⟨by simpa only [map_mul,map_one] using congrArg octahedral_iso_S4 hx,?_⟩
  intro he
  have he' : x=1 := octahedral_iso_S4.injective (he.trans (map_one octahedral_iso_S4).symm)
  have hval : g*q*g⁻¹=1 := congrArg Subtype.val he'
  apply hn
  calc
    q = g⁻¹*(g*q*g⁻¹)*g := by group
    _ = 1 := by rw [hval]; group

/-- No row is a supplied classification premise: the finite commuting pair
chooses it, and the residual simultaneous centralizer fixes the whole group. -/
theorem group_is_marked (H : Subgroup (PGL2 ℂ))
    (hx : xClass∈H) (hz : zClass∈H)
    (model : HasModel H (.platonic .octahedral)) :
    ∃ f : Form, H=Models.group f := by
  obtain ⟨g,hG⟩ := model
  have image_mem (q : PGL2 ℂ) (hq : q∈H) : g*q*g⁻¹∈modelPGL .octahedral := by
    rw [←hG]
    exact ⟨q,hq,rfl⟩
  let x : modelPGL .octahedral := ⟨g*xClass*g⁻¹,image_mem xClass hx⟩
  let j : modelPGL .octahedral := ⟨g*zClass*g⁻¹,image_mem zClass hz⟩
  have hxi : Involution (octahedral_iso_S4 x) :=
    conj_involution g xClass (by simpa only [pow_two] using xClass_square)
      pauli_x_ne_one (image_mem xClass hx)
  have hji : Involution (octahedral_iso_S4 j) :=
    conj_involution g zClass (by simpa only [pow_two] using zClass_square)
      pauli_z_ne_one (image_mem zClass hz)
  obtain ⟨f,hf⟩ := pair_type_exists _ _ hxi hji
  have hc : Commute x j := Subtype.ext
    ((xClass_commute_zClass.map (MulAut.conj g).toMonoidHom).eq)
  have hne : x≠j := by
    intro he
    exact pauli_x_ne_z ((MulAut.conj g).injective (congrArg Subtype.val he))
  obtain ⟨c,ha,hb⟩ := literal_pair f x j hxi hji hf hc hne
  let u : PGL2 ℂ := (c : PGL2 ℂ)*g
  have hU : H.map (MulAut.conj u).toMonoidHom=modelPGL .octahedral := by
    rw [show u=(c : PGL2 ℂ)*g from rfl,map_conj_mul,hG]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((modelPGL .octahedral).le_normalizer c.property)
  have huX : u*xClass*u⁻¹=Models.p f*xClass*(Models.p f)⁻¹ := by
    calc
      _ = (c : PGL2 ℂ)*(g*xClass*g⁻¹)*(c : PGL2 ℂ)⁻¹ := by dsimp [u]; group
      _ = (indexedPGL .octahedral (Models.xIndex f) : PGL2 ℂ) := congrArg Subtype.val ha
      _ = _ := (Models.basis_x f).symm
  have huZ : u*zClass*u⁻¹=Models.p f*zClass*(Models.p f)⁻¹ := by
    calc
      _ = (c : PGL2 ℂ)*(g*zClass*g⁻¹)*(c : PGL2 ℂ)⁻¹ := by dsimp [u]; group
      _ = (indexedPGL .octahedral (Models.zIndex f) : PGL2 ℂ) := congrArg Subtype.val hb
      _ = _ := (Models.basis_z f).symm
  let n := (Models.p f)⁻¹*u
  have fixed (q : PGL2 ℂ) (hu : u*q*u⁻¹=Models.p f*q*(Models.p f)⁻¹) : n*q*n⁻¹=q := by
    calc
      _ = (Models.p f)⁻¹*(u*q*u⁻¹)*Models.p f := by dsimp [n]; group
      _ = (Models.p f)⁻¹*(Models.p f*q*(Models.p f)⁻¹)*Models.p f := by rw [hu]
      _ = q := by group
  have comm {q : PGL2 ℂ} (hq : n*q*n⁻¹=q) : Commute n q := by
    apply (commute_iff_eq _ _).mpr
    have he := congrArg (fun r : PGL2 ℂ => r*n) hq
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using he
  have hn : n∈pauliSubgroup := (pauli_membership n).mpr ((commute_x_z_iff n).mp
    ⟨comm (fixed xClass huX),comm (fixed zClass huZ)⟩)
  have hPH : pauliSubgroup≤H := by
    change Subgroup.closure _≤H
    rw [Subgroup.closure_le]
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl|hq
    · exact hx
    · exact (Set.mem_singleton_iff.mp hq).symm ▸ hz
  have hN := Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer (hPH hn))
  refine ⟨f,?_⟩
  calc
    H = H.map (MulAut.conj n).toMonoidHom := hN.symm
    _ = (modelPGL .octahedral).map (MulAut.conj (Models.p f)⁻¹).toMonoidHom := by
      rw [show n=(Models.p f)⁻¹*u from rfl,map_conj_mul,hU]
    _ = Models.group f := rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Coordinates.Alignment
