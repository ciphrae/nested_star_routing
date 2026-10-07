import NestedRouting.Star.Layout

/-! One service of a star router on one spoke. With the blank at the loop
start `x j`, the blank walks the export lane to the child's blank cell,
optionally calls the child's request on the delivery head, and walks back
along the delivery lane and the hub cell `H j`. The export queue shifts
toward the hub (its head lands in `H j`), the child's output joins its
tail, the delivery queue shifts toward the child and `H j`'s tile joins
its tail. -/
namespace SlidingPuzzle.NestedRouting.Interface
open Finset TileRoles
open SlidingPuzzle.NestedRouting.ReservePolicy

variable {n : Nat} [NeZero n] {J : Nat} {Q : Fin J → Region n} (L : StarLayout n J Q)

namespace StarLayout

theorem out_nodup (j : Fin J) : (L.x j :: L.exportQ j).Nodup := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportQ j)++(L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf,exportQ]
  rw [split] at h
  exact (List.nodup_append.mp h).1

theorem back_nodup (j : Fin J) : (L.z j :: (L.e j :: L.deliveryLane j++[L.hub (L.H j),L.x j])).Nodup := by
  have h := L.loop_nodup j
  simp only [loopOf,List.cons_append,List.append_assoc,List.nodup_cons,List.nodup_append,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.nodup_nil] at h ⊢
  aesop

theorem out_sub_loop (j : Fin J) {c : Cell n} (hc : c∈L.x j :: L.exportQ j) : c∈L.loop j := by
  rcases List.mem_cons.mp hc with rfl | hc
  · exact L.x_mem_loop j
  · exact L.mem_loop_of_exportQ hc

theorem back_sub_loop (j : Fin J) {c : Cell n}
    (hc : c∈L.z j :: (L.e j :: L.deliveryLane j++[L.hub (L.H j),L.x j])) : c∈L.loop j := by
  simp only [List.mem_cons,List.mem_append] at hc
  simp only [loop,loopOf,List.mem_cons,List.mem_append]
  tauto

theorem e_notMem_out (j : Fin J) : L.e j∉L.x j :: L.exportQ j := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportQ j)++(L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf,exportQ]
  rw [split] at h
  exact fun he => List.disjoint_of_nodup_append h he (by simp)

theorem deliveryLane_notMem_out (j : Fin J) {c : Cell n} (hc : c∈L.deliveryLane j) :
    c∉L.x j :: L.exportQ j := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportQ j)++(L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf,exportQ]
  rw [split] at h
  exact fun hm => List.disjoint_of_nodup_append h hm (by simp [hc])

theorem H_notMem_out (j : Fin J) : L.hub (L.H j)∉L.x j :: L.exportQ j := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportQ j)++(L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf,exportQ]
  rw [split] at h
  exact fun hm => List.disjoint_of_nodup_append h hm (by simp)

theorem exportLane_notMem_back (j : Fin J) {c : Cell n} (hc : c∈L.exportLane j) :
    c∉L.z j :: (L.e j :: L.deliveryLane j++[L.hub (L.H j),L.x j]) := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportLane j)++(L.z j :: L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf]
  rw [split] at h
  have hx : L.x j∉L.exportLane j := (List.nodup_cons.mp (List.nodup_append.mp h).1).1
  intro hm
  have : c=L.x j ∨ c∈(L.z j :: L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp only [List.mem_cons,List.mem_append] at hm ⊢
    tauto
  rcases this with rfl | hm'
  · exact hx hc
  · exact List.disjoint_of_nodup_append h (List.mem_cons_of_mem _ hc) hm'

theorem e_notMem_tail (j : Fin J) : L.e j∉L.deliveryLane j++[L.hub (L.H j)] := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportQ j)++(L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf,exportQ]
  rw [split] at h
  exact (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1

theorem deliveryLane_ne_e (j : Fin J) {c : Cell n} (hc : c∈L.deliveryLane j) : c≠L.e j := by
  rintro rfl
  exact L.e_notMem_tail j (List.mem_append_left _ hc)

theorem getLast_out (j : Fin J) :
    (L.x j :: L.exportQ j).getLast (List.cons_ne_nil _ _)=L.z j := by
  simp [exportQ]

theorem getLast_back (j : Fin J) :
    (L.z j :: (L.e j :: L.deliveryLane j++[L.hub (L.H j),L.x j])).getLast (List.cons_ne_nil _ _)=L.x j := by
  simp

/-- The loop part of a service, with the blank at `x j`. -/
theorem exists_loop (j : Fin J) {B : Board n} (atX : blank B=L.x j) {β : Nat} {s : (Q j).Rec}
    (hs : (Q j).Holds β s B) (act : Option Arrival)
    (valid : ∀ a, act=some a → (Q j).Label a (B (L.e j)) ∧
      RequestGuard (Q j).M (Q j).r ((Q j).counts s) a ∧
      Lead β (advance ((Q j).counts s) a (select (Q j).M (Q j).r ((Q j).counts s) a))) :
    ∃ D : Board n, ∃ q : Path B D, ∃ next : (Q j).Rec, ∃ out : Tile n,
      blank D=L.x j ∧ (Q j).Holds β next D ∧
      D (L.hub (L.H j)) :: (L.exportQ j).map D=(L.exportQ j).map B++[out] ∧
      B (L.e j) :: (L.deliveryQ j).map D=(L.deliveryQ j).map B++[B (L.hub (L.H j))] ∧
      (∀ y, y∉L.loop j → y∉(Q j).cells → D y=B y) ∧
      q.length+(Q j).work s≤(L.exportQ j).length+(L.deliveryQ j).length+2+(Q j).work next ∧
      ((act=none ∧ next=s ∧ out=B (L.e j)) ∨
        (∃ a, act=some a ∧ out∈(Q j).roles s (select (Q j).M (Q j).r ((Q j).counts s) a).role ∧
          (Q j).roles next=updateRoles ((Q j).roles s) out (B (L.e j)) a.role ∧
          (Q j).counts next=advance ((Q j).counts s) a (select (Q j).M (Q j).r ((Q j).counts s) a))) := by
  classical
  obtain ⟨B3,p3,len3,eff3⟩ := exists_walk (L.x j) (L.exportQ j) (L.out_chain j) B atX
  have blank3 : blank B3=L.z j := (walk_blank _ _ eff3 atX).trans (L.getLast_out j)
  have offOut (y : Cell n) (hy : y∉L.x j :: L.exportQ j) : B3 y=B y := walk_fixed _ eff3 hy
  have childOut (y : Cell n) (hy : y∈(Q j).cells) : y∉L.x j :: L.exportQ j :=
    fun hm => L.loop_child j j y (L.out_sub_loop j hm) hy
  have hs3 : (Q j).Holds β s B3 := (Q j).transport hs p3 (fun y hy => offOut y (childOut y hy))
  have e3 : B3 (L.e j)=B (L.e j) := offOut _ (L.e_notMem_out j)
  -- the optional request
  have mid : ∃ R : Board n, ∃ pR : Path B3 R, ∃ next : (Q j).Rec,
      (Q j).Holds β next R ∧ blank R=L.z j ∧
      (∀ y, y∉(Q j).cells → y≠L.e j → R y=B3 y) ∧
      pR.length+(Q j).work s≤(Q j).work next ∧
      ((act=none ∧ next=s ∧ R (L.e j)=B (L.e j)) ∨
        (∃ a, act=some a ∧ R (L.e j)∈(Q j).roles s (select (Q j).M (Q j).r ((Q j).counts s) a).role ∧
          (Q j).roles next=updateRoles ((Q j).roles s) (R (L.e j)) (B (L.e j)) a.role ∧
          (Q j).counts next=advance ((Q j).counts s) a (select (Q j).M (Q j).r ((Q j).counts s) a))) := by
    cases hact : act with
    | none => exact ⟨B3,.nil B3,s,hs3,blank3,fun _ _ _ => rfl,by simp,Or.inl ⟨rfl,rfl,e3⟩⟩
    | some a =>
      obtain ⟨label,guard,lead⟩ := valid a hact
      obtain ⟨r⟩ := (Q j).request a hs3 (L.entry j) blank3 (e3 ▸ label) guard lead
      refine ⟨r.board,r.path,r.next,r.holds,r.blank.trans blank3,r.fixed,?_,Or.inr ⟨a,rfl,r.exported,?_,r.counts⟩⟩
      · have := r.work; omega
      · rw [r.roles,e3]
  obtain ⟨R,pR,next,holdsR,blankR,fixedR,workR,outcome⟩ := mid
  obtain ⟨D,p5,len5,eff5⟩ := exists_walk (L.z j) _ (L.back_chain j) R blankR
  have blankD : blank D=L.x j := (walk_blank _ _ eff5 blankR).trans (L.getLast_back j)
  have offBack (y : Cell n) (hy : y∉L.z j :: (L.e j :: L.deliveryLane j++[L.hub (L.H j),L.x j])) :
      D y=R y := walk_fixed _ eff5 hy
  have holdsD : (Q j).Holds β next D :=
    (Q j).transport holdsR p5 (fun y hy => offBack y (fun hm => L.loop_child j j y (L.back_sub_loop j hm) hy))
  -- the contents identities
  have c3 := walk_contents (L.x j) (L.exportQ j) (L.out_nodup j) eff3
  have c5 := walk_contents (L.z j) _ (L.back_nodup j) eff5
  have c3' : (B3 (L.x j) :: (L.exportLane j).map B3)++[B3 (L.z j)]=
      ((L.exportLane j).map B++[B (L.z j)])++[B (L.x j)] := by simpa [exportQ] using c3
  obtain ⟨hx3,-⟩ := List.append_inj c3' (by simp)
  have c5' : D (L.z j) :: ((D (L.e j) :: (L.deliveryLane j).map D)++[D (L.hub (L.H j)),D (L.x j)])=
      R (L.e j) :: (((L.deliveryLane j).map R++[R (L.hub (L.H j))])++[R (L.x j),R (L.z j)]) := by
    simpa using c5
  obtain ⟨hz5,rest5⟩ := List.cons_eq_cons.mp c5'
  obtain ⟨hdel,htail⟩ := List.append_inj rest5 (by simp)
  have hH5 : D (L.hub (L.H j))=R (L.x j) := (List.cons_eq_cons.mp htail).1
  -- cells off the child and the input keep their `B3` value under the request
  have keepR (y : Cell n) (hl : y∈L.loop j) (hy : y≠L.e j) : R y=B3 y :=
    fixedR y (fun hq => L.loop_child j j y hl hq) hy
  have xNe : L.x j≠L.e j := fun he => L.e_notMem_out j (he ▸ List.mem_cons_self)
  refine ⟨D,(p3.append pR).append p5,next,R (L.e j),blankD,holdsD,?_,?_,?_,?_,?_⟩
  · have laneD : (L.exportLane j).map D=(L.exportLane j).map B3 := by
      apply List.map_congr_left
      intro y hy
      have hq : y∈L.exportQ j := by simp [exportQ,hy]
      rw [offBack y (L.exportLane_notMem_back j hy)]
      apply keepR y (L.mem_loop_of_exportQ hq)
      intro he
      exact L.e_notMem_out j (he ▸ List.mem_cons_of_mem _ hq)
    rw [hH5,keepR _ (L.x_mem_loop j) xNe]
    simp only [exportQ,List.map_append,List.map_singleton,laneD,hz5]
    rw [←List.cons_append,hx3]
  · have laneR : (L.deliveryLane j).map R=(L.deliveryLane j).map B := by
      apply List.map_congr_left
      intro y hy
      rw [keepR y (L.mem_loop_of_deliveryQ (by simp [deliveryQ,hy])) (L.deliveryLane_ne_e j hy)]
      exact offOut y (L.deliveryLane_notMem_out j hy)
    have hHR : R (L.hub (L.H j))=B (L.hub (L.H j)) := by
      rw [keepR _ (L.H_mem_loop j) ?_]
      · exact offOut _ (L.H_notMem_out j)
      · intro he
        exact L.e_notMem_tail j (he ▸ List.mem_append_right _ (List.mem_singleton_self _))
    simp only [deliveryQ,List.map_cons,hdel,laneR,hHR,List.cons_append]
  · intro y hl hq
    have hb : y∉L.z j :: (L.e j :: L.deliveryLane j++[L.hub (L.H j),L.x j]) :=
      fun hm => hl (L.back_sub_loop j hm)
    have ho : y∉L.x j :: L.exportQ j := fun hm => hl (L.out_sub_loop j hm)
    rw [offBack y hb,fixedR y hq (fun he => hl (he ▸ L.mem_loop_of_deliveryQ (L.e_mem_deliveryQ j))),
      offOut y ho]
  · simp only [Path.length_append,len3,len5]
    simp only [deliveryQ,List.length_cons,List.length_append,List.length_nil]
    omega
  · rcases outcome with ⟨h1,h2,h3⟩ | ⟨a,h1,h2,h3,h4⟩
    · exact Or.inl ⟨h1,h2,h3⟩
    · exact Or.inr ⟨a,h1,h2,h3,h4⟩

theorem ne_zero_of_ne_blank {B : Board n} {y : Cell n} (h : y≠blank B) : B y≠0 := by
  intro hz
  exact h (B.symm_apply_eq.mpr hz.symm).symm

theorem x_mem_access (j : Fin J) : L.x j∈L.access j := by
  rw [←L.access_last j]
  exact List.getLast_mem _

theorem H_notMem_access (j : Fin J) : L.hub (L.H j)∉L.access j := by
  intro hm
  have hx := L.access_loop j _ hm (L.H_mem_loop j)
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportQ j)++(L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf,exportQ]
  rw [split] at h
  exact List.disjoint_of_nodup_append h (List.mem_cons_self) (hx ▸ (by simp))

theorem notMem_access_of_loop (j : Fin J) {c : Cell n} (hl : c∈L.loop j) (hx : c≠L.x j) :
    c∉L.access j := fun ha => hx (L.access_loop j c ha hl)

theorem x_notMem_deliveryQ (j : Fin J) : L.x j∉L.deliveryQ j := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportQ j)++(L.e j :: L.deliveryLane j++[L.hub (L.H j)]) := by
    simp [loopOf,exportQ]
  rw [split] at h
  intro hm
  exact List.disjoint_of_nodup_append h (List.mem_cons_self)
    (by simp only [deliveryQ,List.mem_cons] at hm ⊢; simp_all)

theorem H_notMem_exportQ (j : Fin J) : L.hub (L.H j)∉L.exportQ j :=
  fun hm => L.H_notMem_out j (List.mem_cons_of_mem _ hm)

theorem H_notMem_deliveryQ (j : Fin J) : L.hub (L.H j)∉L.deliveryQ j := by
  have h := L.loop_nodup j
  have split : loopOf (L.x j) (L.exportLane j) (L.z j) (L.e j) (L.deliveryLane j) (L.hub (L.H j))=
      (L.x j :: L.exportLane j++[L.z j])++((L.e j :: L.deliveryLane j)++[L.hub (L.H j)]) := by
    simp [loopOf]
  rw [split] at h
  have h2 := (List.nodup_append.mp h).2.1
  intro hm
  exact List.disjoint_of_nodup_append h2 hm (List.mem_singleton_self _)

theorem mem_loop_cases (j : Fin J) {y : Cell n} (hl : y∈L.loop j) :
    y=L.x j ∨ y∈L.exportQ j ∨ y∈L.deliveryQ j ∨ y=L.hub (L.H j) := by
  simp only [loop,loopOf,List.cons_append,List.mem_cons,List.mem_append,
    List.not_mem_nil,or_false] at hl
  simp only [exportQ,deliveryQ,List.mem_cons,List.mem_append,
    List.not_mem_nil,or_false]
  rcases hl with h | ((h | h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr h))

/-- One complete service on spoke `j`, starting and ending with the blank
on the park cell `w`. The carrier in `K` joins the delivery queue; the
export head becomes the carrier. -/
theorem exists_service (j : Fin J) {B : Board n} (atW : blank B=L.hub L.w) {β : Nat}
    {s : (Q j).Rec} (hs : (Q j).Holds β s B) (act : Option Arrival)
    (valid : ∀ a, act=some a → (Q j).Label a (B (L.e j)) ∧
      RequestGuard (Q j).M (Q j).r ((Q j).counts s) a ∧
      Lead β (advance ((Q j).counts s) a (select (Q j).M (Q j).r ((Q j).counts s) a))) :
    ∃ C : Board n, ∃ path : Path B C, ∃ next : (Q j).Rec, ∃ out : Tile n,
      blank C=L.hub L.w ∧ (Q j).Holds β next C ∧
      C (L.hub L.K) :: (L.exportQ j).map C=(L.exportQ j).map B++[out] ∧
      B (L.e j) :: (L.deliveryQ j).map C=(L.deliveryQ j).map B++[B (L.hub L.K)] ∧
      (∀ y, y∉L.exportQ j → y∉L.deliveryQ j → y∉(Q j).cells → y≠L.hub L.K → C y=B y) ∧
      path.length+(Q j).work s≤2*L.hcost j+2*(L.accessTail j).length+
        (L.exportQ j).length+(L.deliveryQ j).length+2+(Q j).work next ∧
      ((act=none ∧ next=s ∧ out=B (L.e j)) ∨
        (∃ a, act=some a ∧ out∈(Q j).roles s (select (Q j).M (Q j).r ((Q j).counts s) a).role ∧
          (Q j).roles next=updateRoles ((Q j).roles s) out (B (L.e j)) a.role ∧
          (Q j).counts next=advance ((Q j).counts s) a (select (Q j).M (Q j).r ((Q j).counts s) a))) := by
  classical
  -- first hub cycle: the carrier into `H`, the third cell's token into `K`, `H`'s helper into it
  obtain ⟨B1,p1,len1,blank1,sH1,sK1,su1,fix1'⟩ := L.hX j B atW
  have blank1' : blank B1=L.hub L.w := blank1
  obtain ⟨hKa,-,-⟩ := L.hub_access j
  obtain ⟨hKl,-,-⟩ := L.hub_loop j
  obtain ⟨hKq,-,-⟩ := L.hub_child j
  have hua := L.hc_access j
  have hul := L.hc_loop j
  have huq := L.hc_child j
  have hHq : L.hub (L.H j)∉(Q j).cells := L.loop_child j j _ (L.H_mem_loop j)
  -- three hub cells versus everything else
  have off4 {y : Cell n} (h1 : y≠L.hub L.K) (h2 : y≠L.hub (L.H j)) (h3 : y≠L.hc j) : B1 y=B y :=
    fix1' y h2 h1 h3
  -- access walk
  obtain ⟨B2,p2,len2,eff2⟩ := exists_walk (L.hub L.w) (L.accessTail j) (L.access_chain j) B1 blank1'
  have blank2 : blank B2=L.x j := (walk_blank _ _ eff2 blank1').trans (L.access_last j)
  have offAcc (y : Cell n) (hy : y∉L.access j) : B2 y=B1 y := walk_fixed _ eff2 hy
  have childB2 (y : Cell n) (hy : y∈(Q j).cells) : B2 y=B y := by
    rw [offAcc y (fun ha => L.access_child j y ha hy)]
    apply off4 <;> rintro rfl <;> contradiction
  have hs2 : (Q j).Holds β s B2 := (Q j).transport hs (p1.append p2) childB2
  have eLoop : L.e j∈L.loop j := L.mem_loop_of_deliveryQ (L.e_mem_deliveryQ j)
  have eX : L.e j≠L.x j := fun h => L.x_notMem_deliveryQ j (h ▸ L.e_mem_deliveryQ j)
  have eB2 : B2 (L.e j)=B (L.e j) := by
    rw [offAcc _ (L.notMem_access_of_loop j eLoop eX)]
    apply off4
    · rintro h; exact hKl (h ▸ eLoop)
    · rintro h; exact L.H_notMem_deliveryQ j (h ▸ L.e_mem_deliveryQ j)
    · rintro h; exact hul (h ▸ eLoop)
  -- the loop
  obtain ⟨D,q,next,out,blankD,holdsD,expD,delD,fixD,costD,outcome⟩ :=
    L.exists_loop j blank2 hs2 act (fun a ha => eB2 ▸ valid a ha)
  -- conjugate by the access walk
  obtain ⟨E,r,lenr,blankE,effE⟩ := Path.exists_unstaged p2 q (blankD.trans blank2.symm)
  have blankE' : blank E=L.hub L.w := blankE.trans blank1'
  set σ := (L.access j).formPerm with hσ
  have preimage (y : Cell n) : B2.symm (B1 y)=σ⁻¹ y := by
    apply B2.symm_apply_eq.mpr
    rw [eff2]
    change B1 y=B1 (σ (σ⁻¹ y))
    simp
  have DonAccess (c : Cell n) (hc : c∈L.access j) : D c=B2 c := by
    by_cases hx : c=L.x j
    · subst hx
      have h1 : D (L.x j)=0 := by rw [←blankD]; simp [blank,position]
      have h2 : B2 (L.x j)=0 := by rw [←blank2]; simp [blank,position]
      rw [h1,h2]
    · apply fixD c (fun hl => hx (L.access_loop j c hc hl)) (fun hq => L.access_child j c hc hq)
  have Eacc (y : Cell n) (hy : y∈L.access j) : E y=B1 y := by
    rw [effE,preimage]
    have hm : σ⁻¹ y∈L.access j := by
      rw [←List.formPerm_mem_iff_mem (l:=L.access j)]
      change σ (σ⁻¹ y)∈L.access j
      simpa using hy
    rw [DonAccess _ hm,eff2]
    change B1 (σ (σ⁻¹ y))=B1 y
    simp
  have Eoff (y : Cell n) (hy : y∉L.access j) : E y=D y := by
    rw [effE,preimage]
    congr 1
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (List.formPerm_apply_of_notMem hy).symm
  -- second hub cycle: the new head into `K`, `H`'s helper back, the third cell's token back
  obtain ⟨C,p7,len7,blank7,sK7,sH7,su7,fix7'⟩ := L.hX' j E blankE'
  have fix7 (y : Cell n) (h1 : y≠L.hub L.K) (h2 : y≠L.hub (L.H j)) (h3 : y≠L.hc j) : C y=E y :=
    fix7' y h1 h2 h3
  have HnA := L.H_notMem_access j
  have EK : E (L.hub L.K)=B (L.hc j) := by
    rw [Eoff _ hKa,fixD _ hKl hKq,offAcc _ hKa,sK1]
  have Eu : E (L.hc j)=B (L.hub (L.H j)) := by
    rw [Eoff _ hua,fixD _ hul huq,offAcc _ hua,su1]
  -- loop cells other than `x` and `H` are untouched by the hub swaps and access
  have qCell {y : Cell n} (hl : y∈L.loop j) (hx : y≠L.x j) (hH : y≠L.hub (L.H j)) :
      C y=D y ∧ B2 y=B y := by
    have hK : y≠L.hub L.K := fun h => hKl (h ▸ hl)
    have hu : y≠L.hc j := fun h => hul (h ▸ hl)
    have ha := L.notMem_access_of_loop j hl hx
    exact ⟨(fix7 y hK hH hu).trans (Eoff y ha),(offAcc y ha).trans (off4 hK hH hu)⟩
  have expCell {y : Cell n} (hy : y∈L.exportQ j) := qCell (L.mem_loop_of_exportQ hy)
    (fun h => L.x_notMem_exportQ j (h ▸ hy)) (fun h => L.H_notMem_exportQ j (h ▸ hy))
  have delCell {y : Cell n} (hy : y∈L.deliveryQ j) := qCell (L.mem_loop_of_deliveryQ hy)
    (fun h => L.x_notMem_deliveryQ j (h ▸ hy)) (fun h => L.H_notMem_deliveryQ j (h ▸ hy))
  have childC (y : Cell n) (hy : y∈(Q j).cells) : C y=D y := by
    have hK : y≠L.hub L.K := fun h => hKq (h ▸ hy)
    have hH : y≠L.hub (L.H j) := fun h => hHq (h ▸ hy)
    have hu : y≠L.hc j := fun h => huq (h ▸ hy)
    exact (fix7 y hK hH hu).trans (Eoff y (fun ha => L.access_child j y ha hy))
  let back : Path D C := (((p2.append q).reverse).append r).append p7
  refine ⟨C,(p1.append r).append p7,next,out,blank7,
    (Q j).transport holdsD back childC,?_,?_,?_,?_,?_⟩
  · rw [sK7,Eoff _ HnA,List.map_congr_left (fun y hy => (expCell hy).1),expD]
    rw [List.map_congr_left (fun y hy => (expCell hy).2)]
  · have hH2 : B2 (L.hub (L.H j))=B (L.hub L.K) := by rw [offAcc _ HnA,sH1]
    rw [List.map_congr_left (fun y hy => (delCell hy).1),←eB2,delD,hH2,
      List.map_congr_left (fun y hy => (delCell hy).2)]
  · intro y hE hD hq hK
    by_cases hH : y=L.hub (L.H j)
    · subst hH; rw [sH7,Eu]
    by_cases hu : y=L.hc j
    · subst hu; rw [su7,EK]
    rw [fix7 y hK hH hu]
    by_cases ha : y∈L.access j
    · rw [Eacc y ha,off4 hK hH hu]
    · have hl : y∉L.loop j := by
        intro hl
        rcases L.mem_loop_cases j hl with h | h | h | h
        · exact ha (by rw [h]; exact L.x_mem_access j)
        · exact hE h
        · exact hD h
        · exact hH h
      rw [Eoff y ha,fixD y hl hq,offAcc y ha,off4 hK hH hu]
  · simp only [Path.length_append,lenr,len2]
    omega
  · rcases outcome with ⟨h1,h2,h3⟩ | ⟨a,h1,h2,h3,h4⟩
    · exact Or.inl ⟨h1,h2,h3.trans eB2⟩
    · exact Or.inr ⟨a,h1,h2,eB2 ▸ h3,h4⟩

end StarLayout
end SlidingPuzzle.NestedRouting.Interface
