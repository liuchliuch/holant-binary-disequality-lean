import Holant.Proofs.Closure.HistorySectorCardsReceipts

/-! Concrete weighted CURRENT card graphs: transform each already constructed
original-field direct graph at the SAME marked basis. Every vertex, native edge,
incidence port and scalar component is retained. The inverse open-return factory
produces both charged original-G programmes and returns the exact source card.
This constructs analytic weighted graphs, without declaring the basis a gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCardsNetworks
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
open HistorySectorCards
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (U : InvertibleKernel) {n : ℕ}
variable {g : Signature (OI.K G) n} (D : DeckDirect P.family g)

def weighted : Network AlgebraicComplex n :=
  OpenHolographic.transform (D.network.map (algebraicEmbedding G)) U.matrix U.inverse

theorem same_shape : (weighted G P U D).shape = D.network.shape := rfl

theorem labels (v : Fin D.network.shape.vertices) :
    (⟨(weighted G P U D).shape.arity v,(weighted G P U D).vertex v⟩ : AnySignature AlgebraicComplex) ∈
      familyAction U.symm (ClosureMarkedHistoryReceipts.RH.mapFamily (algebraicEmbedding G) P.family) := by
  refine ⟨⟨D.network.shape.arity v,
    ClosurePhysicalBridge.RH.mapSignature (algebraicEmbedding G) (D.network.vertex v)⟩,?_,rfl⟩
  exact ⟨⟨D.network.shape.arity v,D.network.vertex v⟩,D.vertex v,rfl⟩

theorem edges (e : Fin D.network.shape.edges) : (weighted G P U D).edge e = sectorEdge U := by
  change Kernel.pullback (fun a b => algebraicEmbedding G (D.network.edge e a b)) U.matrix = _
  rw [D.edge e]
  have he : (fun a b => algebraicEmbedding G (Signature.disequality (K:=OI.K G) a b)) =
      (Signature.disequality : Mat) := by
    funext a b
    cases a <;> cases b <;> simp [Signature.disequality]
  rw [he]
  rfl

theorem value : (weighted G P U D).denote =
    U.symm.action (HistorySectorCards.RH.mapSignature (algebraicEmbedding G) g) := by
  rw [weighted,OpenHolographic.denote_transform _ _ _ U.matrix_inverse]
  have hm : (D.network.map (algebraicEmbedding G)).denote =
      HistorySectorCards.RH.mapSignature (algebraicEmbedding G) D.network.denote :=
    funext (Network.denote_map _ _)
  rw [hm,D.value]
  rfl

def openReturn : HolographicOpenAccess G P U.symm (weighted G P U D) :=
  fromHolographicOpen G P U.symm (weighted G P U D) (labels G P U D)
    (fun e => (edges G P U D e).trans (HistorySectorTrees.same_edge U).symm)

/-- The inverse return restores the SAME whole mapped original card graph,
including nullary components and every ordered incidence port. -/
theorem restored_exact : (openReturn G P U D).restored = D.network.map (algebraicEmbedding G) :=
  (openReturn G P U D).restoredIdentity.trans
    (restoredOpen_forward U (D.network.map (algebraicEmbedding G)))

/-- Exact source-field endpoint of the returned physical programmes. -/
theorem original_output : (openReturn G P U D).output = g := by
  funext x
  apply (algebraicEmbedding G).injective
  have h := (openReturn G P U D).mappedOutput
  rw [value,InvertibleKernel.symm_symm,U.action_symm_action] at h
  exact congrFun h x

variable (torsion : ResidualTorsion P.family) {m : ℕ}
variable (f : Signature (OI.K G) (m+2)) (core : MinimumCore P.family)
variable (hcore : core.signature = ⟨m+2,f⟩)

def raw (key : RawCardKey m (completeGroup P.family torsion)) : Network AlgebraicComplex m :=
  weighted G P U (deckRawDirect G P torsion f core hcore key)

theorem raw_value (key : RawCardKey m (completeGroup P.family torsion)) :
    (raw G P U torsion f core hcore key).denote =
      card (algebraicEmbedding G) U P.family torsion f key :=
  (value G P U (deckRawDirect G P torsion f core hcore key)).trans
    (card_transport (algebraicEmbedding G) U P.family torsion f key)

def rawReturn (key : RawCardKey m (completeGroup P.family torsion)) :
    HolographicOpenAccess G P U.symm (raw G P U torsion f core hcore key) :=
  openReturn G P U (deckRawDirect G P torsion f core hcore key)

theorem raw_original_output (key : RawCardKey m (completeGroup P.family torsion)) :
    (rawReturn G P U torsion f core hcore key).output = rawCard P.family torsion f key :=
  original_output G P U (deckRawDirect G P torsion f core hcore key)

/-- Thin specialization to the SAME previously returned current-deck receipt.
No core, stable proof, basis, physical programme or replacement graph is chosen. -/
def receiptRaw (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (key : RawCardKey m (completeGroup P.family torsion)) : Network AlgebraicComplex m :=
  weighted G P U (R.current.raw key)

theorem receiptRaw_value (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (key : RawCardKey m (completeGroup P.family torsion)) :
    (receiptRaw G P U torsion f R key).denote = card (algebraicEmbedding G) U P.family torsion f key :=
  (value G P U (R.current.raw key)).trans (R.cardIdentity key).symm

def receiptRawReturn (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (key : RawCardKey m (completeGroup P.family torsion)) :
    HolographicOpenAccess G P U.symm (receiptRaw G P U torsion f R key) :=
  openReturn G P U (R.current.raw key)

theorem receiptRaw_original_output (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (key : RawCardKey m (completeGroup P.family torsion)) :
    (receiptRawReturn G P U torsion f R key).output = rawCard P.family torsion f key :=
  original_output G P U (R.current.raw key)

/-- Entire CURRENT deck, including its separately charged standalone zero. -/
def receiptDeck (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (g : Signature (OI.K G) m) (hg : g ∈ rawDeck P.family torsion f) : Network AlgebraicComplex m :=
  weighted G P U (R.current.entireRawDeck g hg)

theorem receiptDeck_value (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (g : Signature (OI.K G) m) (hg : g ∈ rawDeck P.family torsion f) :
    (receiptDeck G P U torsion f R g hg).denote =
      U.symm.action (HistorySectorCards.RH.mapSignature (algebraicEmbedding G) g) :=
  value G P U (R.current.entireRawDeck g hg)

def receiptDeckReturn (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (g : Signature (OI.K G) m) (hg : g ∈ rawDeck P.family torsion f) :
    HolographicOpenAccess G P U.symm (receiptDeck G P U torsion f R g hg) :=
  openReturn G P U (R.current.entireRawDeck g hg)

theorem receiptDeck_original_output (R : HistorySectorCardsReceipts.Receipt G P torsion f U)
    (g : Signature (OI.K G) m) (hg : g ∈ rawDeck P.family torsion f) :
    (receiptDeckReturn G P U torsion f R g hg).output = g :=
  original_output G P U (R.current.entireRawDeck g hg)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCardsNetworks
end
