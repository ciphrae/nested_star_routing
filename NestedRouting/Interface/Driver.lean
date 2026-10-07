import NestedRouting.Interface.Region

/-! The top-level feedback driver. A region whose core and reserve cells
hold only its own goal tiles is solved by feeding every exported tile
straight back in: one helper request first, then one goal arrival per goal.
The lead stays at one throughout, so the whole run, finishing included,
costs at most the region's budget at allowance one. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n]

namespace Region
variable (R : Region n) (B : Board n) (e z : Cell n)

def Goals : Finset (Tile n) := R.coreGoals∪R.reserveGoals

/-- Sources are goal tiles. -/
def SrcGood (s : R.Rec) : Prop :=
  ∀ t, t∈R.roles s .coreSource ∨ t∈R.roles s .reserveSource → t∈R.Goals

/-- After `k` goal arrivals (and the first helper request): the lead is one
and the tile waiting at the input is a goal. -/
def Stage (k : Nat) : Prop :=
  ∃ s : R.Rec, ∃ C : Board n, ∃ p : Path B C,
    R.Holds 1 s C ∧ blank C=z ∧ (∀ x, x∉R.cells → x∉R.strip → C x=B x) ∧
    p.length≤R.work s ∧ (R.counts s).ac+(R.counts s).ar=k ∧ (R.counts s).ec+(R.counts s).er=k+1 ∧
    C e∈R.Goals ∧ R.SrcGood s

variable {R B e z}

theorem srcGood_update {s s' : R.Rec} (h : R.SrcGood s) {old fresh : Tile n} {d : Role}
    (hd : d≠.coreSource ∧ d≠.reserveSource) (hr : R.roles s'=updateRoles (R.roles s) old fresh d) :
    R.SrcGood s' := by
  intro t ht
  rw [hr] at ht
  simp only [mem_updateRoles] at ht
  apply h
  rcases ht with (⟨h1,_⟩ | ⟨_,h2⟩) | (⟨h1,_⟩ | ⟨_,h2⟩)
  · exact absurd h1.symm hd.1
  · exact Or.inl h2
  · exact absurd h1.symm hd.2
  · exact Or.inr h2

theorem exported_good {s : R.Rec} (h : R.SrcGood s) {M r : Nat} {c : Counts} {input : Arrival} {t : Tile n}
    (hsel : select M r c input≠.helper) (ht : t∈R.roles s (select M r c input).role) : t∈R.Goals := by
  apply h
  revert hsel ht
  cases select M r c input <;> intro hsel ht
  · exact Or.inl ht
  · exact Or.inr ht
  · exact absurd rfl hsel

/-- One goal arrival from a stage. -/
theorem arrive {k : Nat} (entry : R.Entry e z) (h : R.Stage B e z k) :
    ∃ s : R.Rec, ∃ C : Board n, ∃ p : Path B C,
      R.Holds 1 s C ∧ blank C=z ∧ (∀ x, x∉R.cells → x∉R.strip → C x=B x) ∧
      p.length≤R.work s ∧ (R.counts s).ac+(R.counts s).ar=k+1 ∧
      (k+1<R.M+R.r → (R.counts s).ec+(R.counts s).er=k+2 ∧ C e∈R.Goals) ∧ R.SrcGood s := by
  obtain ⟨s,C,p,hs,hz,hfix,hlen,hac,hec,hge,hsrc⟩ := h
  have snd := R.sound hs
  obtain ⟨v1,v2,v3,v4,v5,v6⟩ := snd.valid
  have he := R.entry_input entry
  obtain ⟨input,label,hrole⟩ : ∃ input : Arrival, R.Label input (C e) ∧ input≠.helper := by
    rcases mem_union.mp hge with h | h
    · exact ⟨.core,h,by decide⟩
    · exact ⟨.reserve,h,by decide⟩
  have guard : RequestGuard R.M R.r (R.counts s) input := by
    cases input with
    | core => exact snd.guard_core he label
    | reserve => exact snd.guard_reserve he label
    | helper => exact absurd rfl hrole
  have hadv := fun (o : Export) => (show (advance (R.counts s) input o).ac+(advance (R.counts s) input o).ar=
      (R.counts s).ac+(R.counts s).ar+1 ∧
      (advance (R.counts s) input o).ec+(advance (R.counts s) input o).er=
      (R.counts s).ec+(R.counts s).er+(if o=.helper then 0 else 1) by
    cases input <;> cases o <;> simp [advance] <;> first | (exact absurd rfl hrole) | omega)
  have lead : Lead 1 (advance (R.counts s) input (select R.M R.r (R.counts s) input)) := by
    obtain ⟨a1,a2⟩ := hadv (select R.M R.r (R.counts s) input)
    unfold Lead; split_ifs at a2 <;> omega
  obtain ⟨res⟩ := R.request input hs entry hz label guard lead
  obtain ⟨a1,a2⟩ := hadv (select R.M R.r (R.counts s) input)
  rw [←res.counts] at a1 a2
  refine ⟨res.next,res.board,p.append res.path,res.holds,res.blank.trans hz,?_,?_,by omega,?_,?_⟩
  · intro x hx hs'
    have hxe : x≠e := fun h => hs' (h ▸ (R.entry_strip e z entry).1)
    rw [res.fixed x hx hxe]; exact hfix x hx hs'
  · rw [Path.length_append]; have := res.work; omega
  · intro hk
    have hsel : select R.M R.r (R.counts s) input≠.helper := by
      cases input <;> simp only [select] <;> split_ifs <;> first | omega | simp
    refine ⟨by rw [if_neg hsel] at a2; omega,?_⟩
    exact exported_good hsrc hsel res.exported
  · refine srcGood_update hsrc ?_ res.roles
    cases input <;> simp [Arrival.role] at hrole ⊢

theorem stage_zero (entry : R.Entry e z) (hz : blank B=z) (prep : R.Prepared B)
    (hgoals : ∀ x∈R.coreCells∪R.reserveCells, B x∈R.Goals) (hpos : 0<R.M+R.r) : R.Stage B e z 0 := by
  obtain ⟨s0,hs0,hroles,hcounts,hwork⟩ := R.init prep
  have hs := R.relax hs0 (Nat.zero_le 1)
  have label : R.Label .helper (B e) := by
    intro h0
    have hez := (R.entry_strip e z entry).2.2
    apply hez
    rw [←hz]
    simp [blank,position,←h0]
  have guard : RequestGuard R.M R.r (R.counts s0) .helper := by
    rw [hcounts]; change 0<R.M ∨ 0<R.r; omega
  have hsel : select R.M R.r (R.counts s0) .helper≠.helper := by
    simp only [select]; split_ifs <;> simp
  have hadv : (advance (R.counts s0) .helper (select R.M R.r (R.counts s0) .helper)).ac+
      (advance (R.counts s0) .helper (select R.M R.r (R.counts s0) .helper)).ar=0 ∧
      (advance (R.counts s0) .helper (select R.M R.r (R.counts s0) .helper)).ec+
      (advance (R.counts s0) .helper (select R.M R.r (R.counts s0) .helper)).er=1 := by
    rw [hcounts]; simp only [advance,select]; split_ifs <;> simp_all
  have lead : Lead 1 (advance (R.counts s0) .helper (select R.M R.r (R.counts s0) .helper)) := by
    unfold Lead; omega
  have src0 : R.SrcGood s0 := by
    intro t ht
    rw [hroles] at ht
    simp only [Frame.cellRoles] at ht
    rcases ht with ht | ht <;> obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    · exact hgoals x (mem_union_left _ hx)
    · exact hgoals x (mem_union_right _ hx)
  obtain ⟨res⟩ := R.request .helper hs entry hz label guard lead
  rw [←res.counts] at hadv
  refine ⟨res.next,res.board,res.path,res.holds,res.blank.trans hz,?_,?_,hadv.1,hadv.2,
    exported_good src0 hsel res.exported,srcGood_update src0 (by simp [Arrival.role]) res.roles⟩
  · intro x hx hs'
    have hxe : x≠e := fun h => hs' (h ▸ (R.entry_strip e z entry).1)
    exact res.fixed x hx hxe
  · have := res.work; omega

theorem stages (entry : R.Entry e z) (h0 : R.Stage B e z 0) : ∀ k, k<R.M+R.r → R.Stage B e z k := by
  intro k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    obtain ⟨s,C,p,hs,hz,hfix,hlen,hac,hnext,hsrc⟩ := arrive entry (ih (by omega))
    obtain ⟨hec,hge⟩ := hnext hk
    exact ⟨s,C,p,hs,hz,hfix,hlen,hac,hec,hge,hsrc⟩

/-- The feedback run: from a prepared board whose core and reserve cells
hold only goal tiles, every goal is placed within the budget at lead one;
only the region and its strip change, and the blank returns. -/
theorem drive (entry : R.Entry e z) (hz : blank B=z) (prep : R.Prepared B)
    (hgoals : ∀ x∈R.coreCells∪R.reserveCells, B x∈R.Goals) (hpos : 0<R.M+R.r) :
    ∃ C : Board n, ∃ p : Path B C, p.length≤R.budget 1 ∧ blank C=z ∧
      (∀ x, x∉R.cells → x∉R.strip → C x=B x) ∧ ∀ x∈R.coreCells∪R.reserveCells, C x=R.goal x := by
  have hlast := stages entry (stage_zero entry hz prep hgoals hpos) (R.M+R.r-1) (by omega)
  obtain ⟨s,C,p,hs,hzC,hfix,hlen,hac,_,_⟩ := arrive entry hlast
  obtain ⟨v1,v2,v3,v4,v5,v6⟩ := (R.sound hs).valid
  obtain ⟨f⟩ := R.finish hs entry hzC (by omega) (by omega)
  refine ⟨f.board,p.append f.path,?_,f.blank.trans hzC,?_,f.placed⟩
  · rw [Path.length_append]; have := f.cost; omega
  · intro x hx hs'
    rw [f.fixed x hx hs']; exact hfix x hx hs'

end Region
end SlidingPuzzle.NestedRouting.Interface
