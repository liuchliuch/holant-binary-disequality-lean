import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralBinarySupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralFiniteBinary
import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! The no-hardness residual of the actual even-resource selector is a full
nonproduct binary. With a literal Z its first-row ratio has infinite order;
every finite ratio has already been closed by a positive physical bundle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralFullBinarySupply
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace P
export EOQuaternarySparseTract (support mem_support binary_small)
export EOBinaryPlaneClassification (three_obstruction full_product_iff Full Cross)
end P
namespace C
export GeneralEONegativeClosedSupport (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem full_of_closed (f : Signature AlgebraicComplex 2) (closed : C.Closed f)
    (nonproduct : ¬Product f) : P.Full f := by
  classical
  have large : 2<(P.support f).card := by
    by_contra bad
    exact nonproduct (P.binary_small f (by omega))
  have ne3 : (P.support f).card≠3 := by
    intro eqn
    obtain ⟨x,y,z,hx,hy,hz,hole⟩ := P.three_obstruction f eqn
    exact closed x y z hx hy hz hole
  have bound : (P.support f).card≤4 := by
    have h:=Finset.card_le_univ (P.support f)
    norm_num at h
    exact h
  have all : P.support f=Finset.univ := Finset.eq_univ_of_card (P.support f) (by
    have eqn : (P.support f).card=4 := by omega
    simpa using eqn)
  intro x
  apply (P.mem_support f x).mp
  rw [all]
  exact Finset.mem_univ x

variable {s m n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (first : B.Block (s:=src.size) (b:=src.b) m) (second : B.Block (s:=src.size) (b:=src.b) n)
variable (nonaffine : ¬Affine (fun x=>(first.signature src.H x : AlgebraicComplex)))
variable (nonproduct : ¬Product (fun x=>(second.signature src.H x : AlgebraicComplex)))
variable (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G)

include noHard in
theorem full (row : B.Block (s:=src.size) (b:=src.b) 2)
    (bad : ¬Product (fun x=>(row.signature src.H x : AlgebraicComplex))) :
    ∀x,row.signature src.H x≠0 := by
  have h:=full_of_closed _ (NoXGeneralBinarySupply.closed G src noHard row) bad
  intro x zero
  exact h x (congrArg (fun c : src.K=>(c : AlgebraicComplex)) zero)

variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)

include noHard zLiteral in
theorem infinite (row : B.Block (s:=src.size) (b:=src.b) 2)
    (badA : ¬Affine (fun x=>(row.signature src.H x : AlgebraicComplex)))
    (badP : ¬Product (fun x=>(row.signature src.H x : AlgebraicComplex))) :
    ∀k : ℕ,0<k→(row.signature src.H ![false,false]/row.signature src.H ![false,true])^k≠1 := by
  intro k hk eqn
  have live:=full G src noHard row badP
  have det : row.signature src.H ![false,false]*row.signature src.H ![true,true]≠
      row.signature src.H ![false,true]*row.signature src.H ![true,false] := by
    intro zero
    apply badP
    apply (P.full_product_iff _ (full_of_closed _ (NoXGeneralBinarySupply.closed G src noHard row) badP)).mpr
    exact congrArg (fun c : src.K=>(c : AlgebraicComplex)) zero
  have powers : row.signature src.H ![false,false]^k=row.signature src.H ![false,true]^k := by
    rw [div_pow,div_eq_one_iff_eq (pow_ne_zero _ (live _))] at eqn
    exact eqn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  rcases NoXGeneralFiniteBinary.anti_or_hard G src zLabel zLiteral row (live _) (live _) det j powers with hard|⟨anti,v,w,hv,hw,lit⟩
  · exact noHard hard
  · exact noHard (NoXGeneralEvenAntiResources.countingHard G src row row anti v w hv hw lit badA badP)

include nonaffine nonproduct noHard zLiteral in
theorem exists_infinite_binary : ∃row : B.Block (s:=src.size) (b:=src.b) 2,
    (∀x,row.signature src.H x≠0) ∧
    (¬Affine (fun x=>(row.signature src.H x : AlgebraicComplex))) ∧
    (¬Product (fun x=>(row.signature src.H x : AlgebraicComplex))) ∧
    ∀k : ℕ,0<k→(row.signature src.H ![false,false]/row.signature src.H ![false,true])^k≠1 := by
  obtain ⟨row,ha,hp⟩ := NoXGeneralBinarySupply.exists_binary G src first second nonaffine nonproduct noHard
  exact ⟨row,full G src noHard row hp,ha,hp,infinite G src noHard zLabel zLiteral row ha hp⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralFullBinarySupply
end
