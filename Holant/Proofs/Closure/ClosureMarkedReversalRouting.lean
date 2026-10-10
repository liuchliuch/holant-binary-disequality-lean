import Holant.Proofs.Closure.ClosureMarkedReversalOvergroup
import Holant.Proofs.FiniteGroups.UniqueType

/-! Derived native-axis routing of the semantic marked overgroup's dihedral
branch. Pauli inclusion forces even rotation order. Pulling back the actual
central rotation involution proves that one of native X,Z,XZ centralizes the
entire overgroup. The conjugacy witness is used only for routing; it is never
asserted to be an algebraic tensor basis or an actual gadget.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversalRouting
open Holant
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.LocalDrafts.FinitePGL2

/-- All literal displayed dihedral matrices preserve the native coordinate
lines setwise, hence centralize literal Z projectively. -/
theorem dihedral_le_centralizer {m : ℕ} (hm : 0 < m) (ω : ℂˣ)
    (hω : IsPrimitiveRoot ω m) :
    dihedralModel ω ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
  intro q hq
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rcases (mem_dihedralModel_iff hm hω q).mp hq with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
  · exact ((commute_z_iff_entries _).mpr (Or.inl (by simp [diagonalGL,diagonal]))).eq
  · exact ((commute_z_iff_entries _).mpr (Or.inr (by
      simp [xGL,antidiagonalGL,antidiagonal,diagonalGL,diagonal,Matrix.mul_apply]))).eq

/-- Even rotation order makes this coordinate mark a member of the standard
rotation group, rather than merely an external normalizer. -/
theorem z_mem_even_dihedral {m : ℕ} (hm : 0 < m) (heven : Even m) (ω : ℂˣ)
    (hω : IsPrimitiveRoot ω m) : zClass ∈ dihedralModel ω := by
  letI : NeZero m := ⟨Nat.ne_zero_of_lt hm⟩
  have hn : (-1 : ℂ)^m = 1 := heven.neg_one_pow
  obtain ⟨k,hk,he⟩ := hω.eq_pow_of_mem_rootsOfUnity
    ((mem_rootsOfUnity' m (-1 : ℂˣ)).mpr hn)
  apply Or.inl
  apply (mem_cyclicModel_iff hm hω _).mpr
  exact ⟨k,hk,by rw [he]; rfl⟩

/-- A real dihedral conjugacy branch plus actual Pauli inclusion constructs
one of the three literal native centralizer branches. No coordinate selector
or desired centralizer relation is supplied as an assumption. -/
theorem dihedral_native_axis (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hP : pauliSubgroup ≤ H) {m : ℕ} (hm : 2 ≤ m) (ω : ℂˣ)
    (hω : IsPrimitiveRoot ω m) (g : PGL2 ℂ)
    (hmodel : H.map (MulAut.conj g).toMonoidHom = dihedralModel ω) :
    H ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)) ∨
      H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) ∨
      H ≤ Subgroup.centralizer ({xClass*zClass} : Set (PGL2 ℂ)) := by
  have hcard : Nat.card H = 2*m := by
    calc
      Nat.card H = Nat.card (H.map (MulAut.conj g).toMonoidHom) := (card_conjugate_subgroup H g).symm
      _ = 2*m := by rw [hmodel,dihedralModel_card hω]
  have hd := Subgroup.card_dvd_of_le hP
  rw [pauli_card,hcard] at hd
  have hev : Even m := by
    rcases hd with ⟨k,hk⟩
    refine ⟨k,?_⟩
    omega
  have hz := z_mem_even_dihedral (by omega) hev ω hω
  rw [← hmodel] at hz
  obtain ⟨q,hq,hqz⟩ := hz
  have hq1 : q ≠ 1 := by
    intro hq1
    have hz1 : zClass = 1 := by simpa only [hq1,map_one] using hqz.symm
    have ho := zClass_involution
    simp [hz1] at ho
  have hc : ∀ r ∈ H, Commute r q := by
    intro r hr
    have hr' : (MulAut.conj g) r ∈ dihedralModel ω := by
      rw [← hmodel]
      exact ⟨r,hr,rfl⟩
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp
      (dihedral_le_centralizer (by omega) ω hω hr')
    change (MulAut.conj g) r * zClass = zClass * (MulAut.conj g) r at hc'
    rw [← hqz] at hc'
    change (MulAut.conj g) r * (MulAut.conj g) q =
      (MulAut.conj g) q * (MulAut.conj g) r at hc'
    apply (MulAut.conj g).injective
    rw [map_mul,map_mul]
    exact hc' 
  have hp : q ∈ pauliSubgroup := by
    rw [← pauli_self_centralizer]
    apply Subgroup.mem_centralizer_iff.mpr
    intro r hr
    exact (hc r (hP hr)).eq
  have hle : H ≤ Subgroup.centralizer ({q} : Set (PGL2 ℂ)) := by
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hc r hr).eq
  rcases (pauli_membership q).mp hp with h | h | h | h
  · exact (hq1 h).elim
  · exact Or.inl (h ▸ hle)
  · exact Or.inr (Or.inl (h ▸ hle))
  · exact Or.inr (Or.inr (h ▸ hle))

inductive Axis | X | Z | XZ

def Axis.mark : Axis → PGL2 ℂ
  | .X => xClass
  | .Z => zClass
  | .XZ => xClass*zClass

/-- Data selected by the actual finite classification. The Platonic payload
retains its exact semantic group identity; it is not a source hardness exit. -/
inductive Route (H : Subgroup (PGL2 ℂ)) where
  | axis (a : Axis) (centralizes : H ≤ Subgroup.centralizer ({a.mark} : Set (PGL2 ℂ)))
      (m : ℕ) (range : 2 ≤ m) (model : HasModel H (.dihedral m))
  | platonic (p : Holant.Certificates.MatchingProductBridge.PlatonicModel)
      (model : HasModel H (.platonic p))

/-- A closed constructed finite-Pauli routing factory. Cyclicity is ruled out
by the genuine Klein-four inclusion, not by dropping a classification case. -/
def route (H : Subgroup (PGL2 ℂ)) [Finite H] (hP : pauliSubgroup ≤ H) : Route H := by
  classical
  let spec := exists_model H
  let t := Classical.choose spec
  have ht := Classical.choose_spec spec
  cases htype : t with
  | cyclic m =>
      have ht : HasModel H (.cyclic m) := by rw [← htype]; exact ht
      have hf : False := by
        obtain ⟨hm,ω,hω,hconj⟩ := ht
        obtain ⟨e⟩ := hconj.nonempty_mulEquiv
        letI : IsCyclic (cyclicModel ω) := by
          change IsCyclic (Subgroup.zpowers (cyclicGenerator ω))
          infer_instance
        letI : IsCyclic H := isCyclic_of_injective e.toMonoidHom e.injective
        exact IsKleinFour.not_isCyclic (Subgroup.isCyclic_of_le hP)
      exact hf.elim
  | dihedral m =>
      have ht : HasModel H (.dihedral m) := by rw [← htype]; exact ht
      have hm : 2 ≤ m := ht.1
      have ha : H ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)) ∨
          H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) ∨
          H ≤ Subgroup.centralizer ({xClass*zClass} : Set (PGL2 ℂ)) := by
        obtain ⟨ω,hω,g,hg⟩ := ht.2
        exact dihedral_native_axis H hP hm ω hω g hg
      if hx : H ≤ Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)) then
        exact .axis .X hx m hm ht
      else if hz : H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) then
        exact .axis .Z hz m hm ht
      else
        exact .axis .XZ (ha.resolve_left hx |>.resolve_left hz) m hm ht
  | platonic p =>
      have ht : HasModel H (.platonic p) := by rw [← htype]; exact ht
      exact .platonic p ht

namespace Source
open Holant.Tractable Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosureMarkedDihedral.Source
open ClosureMarkedReversalOvergroup.Ambient
variable {L : Type*} [Field L] [NumberField L]

/-- Concrete actual-family factory. Ambient completeness/finiteness, Pauli
inclusion and the semantic adjoin are all constructed from the source. -/
def route (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (Signature.equality : Holant.Certificates.MatchingContractionClosure.Binary (K:=L))⟩ :
        AnySignature L) ∈ F) : Route (overgroup φ F hτ) := by
  letI := ClosureMarkedReversalOvergroup.Ambient.finite φ F hτ
  exact ClosureMarkedReversalRouting.route _ (pauli_le φ F hτ hI)

/-- Actual complete-group inclusion in the constructed native centralizer,
when the returned semantic route is the real dihedral branch. -/
theorem actual_axis (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (a : Axis) (hc : overgroup φ F hτ ≤ Subgroup.centralizer ({a.mark} : Set (PGL2 ℂ))) :
    group φ F hτ ≤ Subgroup.centralizer ({a.mark} : Set (PGL2 ℂ)) :=
  (ClosureMarkedReversalOvergroup.actual_le _ _).trans hc

end Source
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversalRouting
end
