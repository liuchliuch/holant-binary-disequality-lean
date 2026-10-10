import Holant.Proofs.Closure.ClosureSixPortSectors
import Holant.Proofs.Closure.ClosureSixPortNormal
import Holant.Proofs.Closure.ClosureSixPortProportionalGeometry

/-! Proved corrected-paper direct six-port base in literal standard-M
coordinates. The actual ordered zero-safe root deck internally produces every
sector classification and support normalization, and exposes an exact 1+5 or
2+4 ProperSplit of the given tensor. Every Z/P/C pair is covered; no extra
classifier, FourProducts, alignment, atlas branch, desired factor or common-
nonzero-phase oracle is used. This local geometric theorem does not assert
global Close, arbitrary marked-coordinate deck transport or a complexity exit.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
open Holant.LocalDrafts.FinitePGL2.Stabilization

def PrimitiveSixSplit (h : Signature ℂ 6) : Prop :=
  ∃ a b : AnySignature ℂ, ((a.1=1 ∧ b.1=5) ∨ (a.1=2 ∧ b.1=4)) ∧
    Nonempty (ProperSplit (⟨6,h⟩ : AnySignature ℂ) a b)

/-- Exact nontrivial 1+5 or 2+4 factor of the GIVEN six-port tensor. The full
ordered deck is the only mathematical closure input, including all zeros and
all m=3 phases. Actual fixed rulings and every normalization tag are conclusions. -/
theorem direct_six_port_split {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (nonzero : h ≠ 0) (deck : OrderedRootDeck m h) : PrimitiveSixSplit h := by
  classical
  by_cases vanished : ∃ e : Equiv.Perm (Fin 6), ∃ p : Bool, ZeroSector h e p
  · obtain ⟨e,p,zero⟩ := vanished
    cases classifySector hm h deck e (!p) with
    | proportional dependent =>
      obtain ⟨U,B,split⟩ := zero_proportional_split h e p zero dependent
      exact ⟨⟨2,binaryWord U⟩,⟨4,B⟩,Or.inr ⟨rfl,rfl⟩,split⟩
    | complementary D =>
      have opposite : ZeroSector h e (!(!p)) := by simpa only [Bool.not_not] using zero
      exact ⟨_,_,Or.inr ⟨rfl,rfl⟩,⟨D.zero_split opposite⟩⟩
  · have allNonzero (e : Equiv.Perm (Fin 6)) (p : Bool) : ¬ZeroSector h e p := by
      intro zero
      exact vanished ⟨e,p,zero⟩
    cases classifySector hm h deck (Equiv.refl _) false with
    | proportional evenDependent =>
      cases classifySector hm h deck (Equiv.refl _) true with
      | proportional oddDependent =>
        obtain ⟨r,b,split⟩ := Proportional.proportional_proportional_unary_split hm h deck
          (Equiv.refl _) evenDependent oddDependent (allNonzero _ false) (allNonzero _ true)
        exact ⟨⟨1,pointMass b⟩,⟨5,unaryResidual h r b⟩,Or.inl ⟨rfl,rfl⟩,split⟩
      | complementary oddData =>
        exact (Proportional.actual_proportional_complementary_impossible hm h deck (Equiv.refl _)
          false evenDependent (allNonzero _ false) oddData).elim
    | complementary evenData =>
      cases classifySector hm h deck (Equiv.refl _) true with
      | proportional oddDependent =>
        exact (Proportional.actual_proportional_complementary_impossible hm h deck (Equiv.refl _)
          true oddDependent (allNonzero _ true) evenData).elim
      | complementary oddData =>
        obtain ⟨e,p,zero⟩ := complementary_complementary_has_zero_sector h deck
          (Equiv.refl _) evenData oddData
        exact (allNonzero e p zero).elim

/-- The same exact constructed factor excludes tensor primality. -/
theorem direct_six_port_not_prime {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (nonzero : h ≠ 0) (deck : OrderedRootDeck m h) : ¬Prime (⟨6,h⟩ : AnySignature ℂ) := by
  obtain ⟨a,b,arity,split⟩ := direct_six_port_split hm h nonzero deck
  exact fun prime => prime.2 ⟨a,b,split⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
