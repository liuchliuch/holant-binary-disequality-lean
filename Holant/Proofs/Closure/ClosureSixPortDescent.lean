import Holant.Proofs.Closure.ClosureSixPortBase
import Holant.Proofs.Closure.ClosureSixPortNative

/-! Proved exact ORIGINAL-field consequence of the closed literal native-M
six-port base. Actual CURRENT rawDeck stability supplies every root-phase card;
original-field pivot ratios preserve both factor arities and the exact partition
ports, and normalize the descended scale to1 after absorbing the ambient scale
into a factor of a 1+5 or 2+4 proper split. This is coefficient descent,
not a new physical factor-access backend, global Close or arbitrary marked-
coordinate transport. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization

/-- Strengthened pivot descent retaining exact factor arities and ports,
then normalizing the descended scale to1 after absorbing the ambient scale into
a factor. The original tensor's coefficients determine both target factors. -/
theorem exact_split_descent {L E : Type*} [Field L] [Field E] (φ : L →+* E)
    (f : AnySignature L) (nonzero : f.2 ≠ 0) {a b : AnySignature E}
    (s : ProperSplit (Holant.LocalDrafts.FinitePGL2.Stabilization.mapSignature φ f) a b) :
    ∃ u : Signature L a.1, ∃ v : Signature L b.1,
      ∃ t : ProperSplit f ⟨a.1,u⟩ ⟨b.1,v⟩, t.ports=s.ports ∧ t.scale=1 := by
  let join : (Fin a.1 → Bool) → (Fin b.1 → Bool) → (Fin f.1 → Bool) :=
    fun x y i => Sum.elim x y (s.ports.symm i)
  let table := fun x y => f.2 (join x y)
  have reconstruct (x : Fin f.1 → Bool) :
      join (fun i => x (s.ports (.inl i))) (fun j => x (s.ports (.inr j)))=x := by
    funext i
    have all (z : Fin a.1 ⊕ Fin b.1) :
        Sum.elim (fun j => x (s.ports (.inl j))) (fun j => x (s.ports (.inr j))) z=x (s.ports z) := by
      cases z <;> rfl
    exact (all (s.ports.symm i)).trans (congrArg x (s.ports.apply_symm_apply i))
  have tableNonzero : table ≠ 0 := by
    intro zero
    apply nonzero
    funext x
    have he := congrFun (congrFun zero (fun i => x (s.ports (.inl i))))
      (fun j => x (s.ports (.inr j)))
    simpa only [table,reconstruct,Pi.zero_apply] using he
  have equation : ∀ x y, φ (table x y)=((s.scale:E)*a.2 x)*b.2 y := by
    intro x y
    have he := congrFun s.equation (join x y)
    simpa [Holant.LocalDrafts.FinitePGL2.Stabilization.mapSignature,table,join,mul_assoc] using he
  obtain ⟨u,v,hu,hv,factors⟩ := Holant.Algebraic.FactorDescent.exists_exact_factorization
    φ table (fun x => (s.scale:E)*a.2 x) b.2 equation tableNonzero
  refine ⟨u,v,{left_pos:=s.left_pos,right_pos:=s.right_pos,ports:=s.ports,scale:=1,equation:=?_},rfl,rfl⟩
  funext x
  have he := factors (fun i => x (s.ports (.inl i))) (fun j => x (s.ports (.inr j)))
  simp only [table,reconstruct] at he
  simp only [Units.val_one,one_mul]
  convert he using 1 <;> rfl

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)

def OriginalPrimitiveSixSplit (h : Signature (OI.K G) 6) : Prop :=
  ∃ a b : AnySignature (OI.K G), ((a.1=1 ∧ b.1=5) ∨ (a.1=2 ∧ b.1=4)) ∧
    Nonempty (ProperSplit (⟨6,h⟩ : AnySignature (OI.K G)) a b)

/-- Closed CURRENT native-M deck to an exact ORIGINAL-field 1+5 or 2+4 split.
There is no supplied sector classification or factor/programme backend. -/
theorem current_direct_six_port_split
    (N : ClosureMarkedDihedral.NativeM
      (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
    (h : Signature (OI.K G) 6) (nonzero : h ≠ 0)
    (stable : ∀ g ∈ rawDeck P.family torsion h, MatchingOrZero (actualTransfers P.family) g) :
    OriginalPrimitiveSixSplit G h := by
  have mappedNonzero : RH.mapSignature (sourceComplex G) h ≠ 0 := by
    intro zero
    apply nonzero
    funext w
    apply (sourceComplex G).injective
    simpa only [RH.mapSignature,Pi.zero_apply,map_zero] using congrFun zero w
  obtain ⟨a,b,arity,⟨split⟩⟩ := direct_six_port_split N.range _ mappedNonzero
    (orderedRootDeck_of_current G P torsion N h stable)
  obtain ⟨u,v,original,ports,unit⟩ := exact_split_descent (sourceComplex G) ⟨6,h⟩ nonzero split
  exact ⟨⟨a.1,u⟩,⟨b.1,v⟩,arity,⟨original⟩⟩

theorem current_direct_six_port_not_prime
    (N : ClosureMarkedDihedral.NativeM
      (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
    (h : Signature (OI.K G) 6) (nonzero : h ≠ 0)
    (stable : ∀ g ∈ rawDeck P.family torsion h, MatchingOrZero (actualTransfers P.family) g) :
    ¬ Prime (⟨6,h⟩ : AnySignature (OI.K G)) := by
  obtain ⟨a,b,arity,split⟩ := current_direct_six_port_split G P torsion N h nonzero stable
  exact fun prime => prime.2 ⟨a,b,split⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
