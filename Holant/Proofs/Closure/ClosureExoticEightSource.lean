import Holant.Proofs.Closure.ClosureExoticFiberSource
import Holant.Proofs.Closure.ClosureExoticFiberEight
import Holant.Proofs.Closure.ClosureSixPortDescent

/-! Actual original-field split at exotic stable arity>=8. Field descent
retains both exact positive arities and ports and absorbs the unit into a factor. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable Holant.Algebraic Holant.Pauli.ExoticKlein
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

theorem current_eight_original_split (P : Palette G) (torsion : ResidualTorsion P.family)
    (cardinal : Nat.card (completeGroup P.family torsion)=4)
    (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
    (exotic : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic)
    (r : ℕ) (large : 0<r) (f : Signature (OI.K G) (2*r+6)) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃ u v : AnySignature (OI.K G),∃ t : ProperSplit (⟨2*r+6,f⟩ : AnySignature (OI.K G)) u v,
      t.scale=1 := by
  let phi := ClosurePhysicalBridge.complexEmbedding G
  let fc := RingHomRealization.mapSignature phi f
  have live : fc≠0 := by
    intro hz
    apply nonzero
    funext x
    apply phi.injective
    simpa only [fc,RingHomRealization.mapSignature,Pi.zero_apply,map_zero] using congrFun hz x
  have safe := ClosureKleinCurrent.current_exotic_ordered G P torsion cardinal noncyclic exotic f stable
  obtain ⟨m,n,hm,hn,ports,u,v,hu,hv,equation⟩ := pair_safe_eight_factor r large fc live safe
  let split : ProperSplit (mapSignature phi (⟨2*r+6,f⟩ : AnySignature (OI.K G))) ⟨m,u⟩ ⟨n,v⟩ :=
    {left_pos:=hm,right_pos:=hn,ports:=ports,scale:=1,equation:=by
      funext x
      change fc x=1*(u (fun i => x (ports (.inl i)))*v (fun i => x (ports (.inr i))))
      rw [one_mul]
      exact congrFun equation x}
  obtain ⟨u',v',t,hports,hscale⟩ := ClosureSixPort.exact_split_descent phi
    (⟨2*r+6,f⟩ : AnySignature (OI.K G)) nonzero split
  exact ⟨⟨m,u'⟩,⟨n,v'⟩,t,hscale⟩

theorem current_eight_not_prime (P : Palette G) (torsion : ResidualTorsion P.family)
    (cardinal : Nat.card (completeGroup P.family torsion)=4)
    (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
    (exotic : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic)
    (r : ℕ) (large : 0<r) (f : Signature (OI.K G) (2*r+6))
    (prime : Prime (⟨2*r+6,f⟩ : AnySignature (OI.K G)))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) : False := by
  obtain ⟨u,v,t,ht⟩ := current_eight_original_split G P torsion cardinal noncyclic exotic
    r large f prime.1 stable
  exact prime.2 ⟨u,v,⟨t⟩⟩

/-- The stable even exotic prime is now at most six; the real six-port finite
base and quaternary physical endpoint remain distinct cases. -/
theorem stable_prime_residual_le_four (P : Palette G) (torsion : ResidualTorsion P.family)
    (cardinal : Nat.card (completeGroup P.family torsion)=4)
    (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
    (exotic : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic)
    {m : ℕ} (f : Signature (OI.K G) (m+2)) (even : Even (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) : m≤4 := by
  by_contra h
  obtain ⟨k,hk⟩ := even
  have hex : ∃ r : ℕ,0<r ∧ m=2*r+4 := ⟨k-3,by omega,by omega⟩
  obtain ⟨r,hr,rfl⟩ := hex
  exact current_eight_not_prime G P torsion cardinal noncyclic exotic r hr f prime stable

def ForExit (P : Palette G) (E : StructuralExit G P) : Prop := match E with
  | .stable m _ _ _ torsion _ _ _ _ _ =>
      ∀ cardinal : Nat.card (completeGroup P.family torsion)=4,
      ∀ noncyclic : ¬IsCyclic (completeGroup P.family torsion),
      ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic → m≤4
  | _ => True

theorem forExit (P : Palette G) (E : StructuralExit G P) : ForExit G P E := by
  cases E with
  | unary => trivial
  | infinite => trivial
  | odd => trivial
  | stable m f proper even torsion core literal noUnary noOdd stable =>
      intro cardinal noncyclic exotic
      apply stable_prime_residual_le_four G P torsion cardinal noncyclic exotic f even
      · simpa only [literal] using core.prime
      · exact stable

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
