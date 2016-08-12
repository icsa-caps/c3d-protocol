--------------------------------------------------------------------------------
-- Murphi model of C3D protocol:
--   Cheng-Chieh Huang, Rakesh Kumar, Marco Elver, Boris Grot, and Vijay Nagarajan.
--   C3D: Mitigating the NUMA Bottleneck via Coherent DRAM Caches.
--   In IEEE/ACM International Symposium on Microarchitecture (MICRO).
--   Taipei, Taiwan, October 2016.
--
-- Coding convention:
-- * All non-function keywords are lowercase!
-- * All globals (types, functions) are UpperCase.
-- * All variables are lower_case.
-- * Constants (as well as enum constants) are ALL_CAPS.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Constants {{{
--------------------------------------------------------------------------------
const
  -- Number of sockets, each with its own private LLCache and DRAMCache.
  NODE_COUNT: 3;
  DATA_VALUES: 2;

  -- Network parameters.
  VC_REQ: 0;  -- Lowest priority
  VC_RES: 1;
  VC_UNB: 2;  -- Highest priority
  NUM_VCS: 3; -- Must match number of VCs above
  NET_MAX: (NODE_COUNT * 2) + 1; -- One for each of LLCache and DRAMCache + Directory.

-- }}}

--------------------------------------------------------------------------------
-- Types {{{
--------------------------------------------------------------------------------
type
  Socket: scalarset(NODE_COUNT);
  Directory: enum { DirMem };
  Node: union { Directory, Socket };
  Level: enum { DRAMCache, LLCache };
  Value: scalarset(DATA_VALUES);

  VCType: 0..NUM_VCS-1;

  MessageType: enum {
            DATA,
            DATA_ACK,
            DOWNGRADE,
            DOWNGRADE_ACK,
            GETS,
            GETX,
            UPGRADE,
            UPGRADE_ACK,
            INV,
            INV_ACK,
            LOAD,
            PUTX,
            PUT_ACK,
            REPLACEMENT,
            STORE
            };

  Message:
    record
      mtype: MessageType;
      dst_lvl: Level;
      src: Node;
      src_lvl: Level;
      vc: VCType;
      data: Value;
  end;

  DirectoryState:
    record
      state: enum {
        DIR_I,      -- Stable: INVALID
        DIR_IM_IA,  -- I->M waiting for INV_ACKs
        DIR_IM_DA,  -- I->M waiting for DATA_ACK
        DIR_S,      -- Stable: SHARED
        DIR_SM_IA,  -- S->M waiting for INV_ACKs
        DIR_SM_DA,  -- S->M waiting for DATA_ACK
        DIR_SM_U_IA,-- S->M (via UPGRADE) waiting for INV_ACKs
        DIR_M,      -- Stable: MODIFIED
        DIR_MM_P,   -- M->M waiting for PUTX
        DIR_MM_DA,  -- M->M waiting for DATA_ACK
        DIR_MS2,    -- M->S waiting for DOWNGRADE_ACK AND PUTX
        DIR_MS1,    -- M->S waiting for DOWNGRADE_ACK OR  PUTX
        DIR_MI      -- M->I
        };

      owner: Socket;
      sharers: multiset [NODE_COUNT] of Socket;
      need_acks: 0..(NODE_COUNT*2);
      data: Value;
    end;

  DRAMCacheState:
    record
      state: enum {
          DC_I,    -- Stable: INVALID
          DC_IS,   -- I->S
          DC_IS_I, -- I->S sunk INV ->I
          DC_IM,   -- I->M
          DC_S,    -- Stable: SHARED
          DC_M,    -- Stable: MODIFIED (in L1)
          DC_SM,   -- S->M
          DC_SM_U  -- S->M (via UPGRADE)
          };
      data: Value;
    end;

  LLCacheState:
    record
      state: enum {
          LLC_I,   -- Stable: INVALID
          LLC_IS,  -- I->S
          LLC_IS_I,-- I->S sunk INV ->I
          LLC_IM,  -- I->M
          LLC_IM_S,-- I->M sunk DOWNGRADE ->S
          LLC_S,   -- Stable: SHARED
          LLC_SM,  -- S->M
          LLC_M,   -- Stable: MODIFIED
          LLC_MI,  -- M->I
          LLC_MS   -- M->S
          };
      data: Value;
      write: Value;
    end;

-- }}}

--------------------------------------------------------------------------------
-- Variables {{{
--------------------------------------------------------------------------------
var
  net:     array [Node]    of multiset [NET_MAX] of Message;
  sockets: array [Socket]  of
            record
              dc:  DRAMCacheState;
              l1c: LLCacheState;
            end;
  dir: DirectoryState;

  -- Auxiliary variables.
  aux_last_write: Value;

-- }}}

--------------------------------------------------------------------------------
-- Common functions {{{
--------------------------------------------------------------------------------

procedure Send(mtype:MessageType;
               dst:Node;
               dst_lvl:Level;
               src:Node;
               src_lvl:Level;
               vc:VCType;
               data:Value);
var
  msg:Message;
begin
  Assert (MultiSetCount(i:net[dst], true) < NET_MAX) "Too many messages";
  msg.mtype   := mtype;
  msg.dst_lvl := dst_lvl;
  msg.src     := src;
  msg.src_lvl := src_lvl;
  msg.vc      := vc;
  msg.data    := data;
  MultiSetAdd(msg, net[dst]);
end;

procedure ErrorUnhandledMsg();
begin
  Error "Unhandled message type!";
end;

procedure ErrorUnhandledState();
begin
  Error "Unhandled state!";
end;

-- }}}

--------------------------------------------------------------------------------
-- Directory functions {{{
--------------------------------------------------------------------------------

procedure AddToSharersList(s:Socket);
begin
  if MultiSetCount(i:dir.sharers, dir.sharers[i] = s) = 0
  then
    MultiSetAdd(s, dir.sharers);
  endif;
end;

procedure RemoveFromSharersList(s:Socket);
begin
  MultiSetRemovePred(i:dir.sharers, dir.sharers[i] = s);
end;

procedure SelectiveBroadcastToSockets(t:MessageType;
                                      dst_lvl:Level;
                                      source:Socket;
                                      vc:VCType);
begin
  for n:Node do
    if (IsMember(n, Socket) &
        MultiSetCount(i:dir.sharers, dir.sharers[i] = n) != 0)
    then
      if n != source then
        if IsUndefined(dst_lvl) then
          Send(t, n, LLCache, DirMem, UNDEFINED, vc, UNDEFINED);
          Send(t, n, DRAMCache, DirMem, UNDEFINED, vc, UNDEFINED);
        else
          Send(t, n, dst_lvl, DirMem, UNDEFINED, vc, UNDEFINED);
        endif;
      endif;

      RemoveFromSharersList(n);
    endif;
  endfor;
end;

procedure BroadcastToSockets(t:MessageType;
                             dst_lvl:Level;
                             source:Socket;
                             vc:VCType);
begin
  for n:Node do
    if IsMember(n, Socket) then
      if n != source then
        if IsUndefined(dst_lvl) then
          Send(t, n, LLCache, DirMem, UNDEFINED, vc, UNDEFINED);
          Send(t, n, DRAMCache, DirMem, UNDEFINED, vc, UNDEFINED);
        else
          Send(t, n, dst_lvl, DirMem, UNDEFINED, vc, UNDEFINED);
        endif;
      endif;
    endif;
  endfor;
end;

function DirectoryReceive(msg:Message) : boolean;
var
  num_sharers:0..NODE_COUNT;
  is_src_sharer:0..1;
  event:MessageType;
begin
  num_sharers := MultiSetCount(i:dir.sharers, true);
  if MultiSetCount(i:dir.sharers, dir.sharers[i] = msg.src) != 0 then
    is_src_sharer := 1;
  else
    is_src_sharer := 0;
  endif;

  event := msg.mtype;

  switch dir.state
    case DIR_I:
      switch event
        case GETS:
          Send(DATA, msg.src, msg.src_lvl, DirMem, UNDEFINED, VC_RES, dir.data);

        case GETX:
          BroadcastToSockets(INV, DRAMCache, msg.src, VC_REQ);
          dir.owner := msg.src;
          dir.state := DIR_IM_IA;
          dir.need_acks := NODE_COUNT - 1;

        case UPGRADE:
          BroadcastToSockets(INV, DRAMCache, msg.src, VC_REQ);
          dir.owner := msg.src;
          -- Possibly modified by other and line evicted since request.
          dir.state := DIR_IM_IA;
          dir.need_acks := NODE_COUNT - 1;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_IM_IA:
      switch event
        case GETS:
          -- stall
          return false;

        case GETX:
          -- stall
          return false;

        case UPGRADE:
          return false;

        case INV_ACK:
          dir.need_acks := dir.need_acks - 1;
          if dir.need_acks = 0 then
            Send(DATA, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_RES, dir.data);
            dir.state := DIR_IM_DA;
          endif;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_IM_DA:
      switch event
        case GETS:
          -- stall
          return false;

        case GETX:
          -- stall
          return false;

        case UPGRADE:
          return false;

        case DATA_ACK:
          dir.state := DIR_M;

        case PUTX:
          -- XXX: Copy data to memory.
          dir.data := msg.data;
          Send(PUT_ACK, msg.src, LLCache, DirMem, UNDEFINED, VC_UNB, UNDEFINED);
          dir.state := DIR_MI;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_S:
      switch event
        case GETS:
          AddToSharersList(msg.src);
          Send(DATA, msg.src, msg.src_lvl, DirMem, UNDEFINED, VC_RES, dir.data);

        case GETX:
          if is_src_sharer = 1 & num_sharers = 1 then
            Error "IMPOSSIBLE";
            --Send(DATA, msg.src, msg.src_lvl, DirMem, UNDEFINED, VC_RES, dir.data);
            --dir.owner := msg.src;
            --undefine dir.sharers;
            --dir.state := DIR_M;
          else
            SelectiveBroadcastToSockets(INV, DRAMCache, msg.src, VC_REQ);
            dir.owner := msg.src;
            dir.state := DIR_SM_IA;
            dir.need_acks := num_sharers - is_src_sharer;
          endif;

        case UPGRADE:
          if is_src_sharer = 1 & num_sharers = 1 then
            Error "IMPOSSIBLE";
            --Send(UPGRADE_ACK, msg.src, msg.src_lvl, DirMem, UNDEFINED, VC_RES, UNDEFINED);
            --dir.owner := msg.src;
            --undefine dir.sharers;
            --dir.state := DIR_M;
          else
            SelectiveBroadcastToSockets(INV, DRAMCache, msg.src, VC_REQ);
            dir.owner := msg.src;

            if is_src_sharer = 1 then
              dir.state := DIR_SM_U_IA;
            else
              dir.state := DIR_SM_IA;
            endif;
            dir.need_acks := num_sharers - is_src_sharer;
          endif;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_SM_IA:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case INV_ACK:
          dir.need_acks := dir.need_acks - 1;
          if dir.need_acks = 0 then
            Send(DATA, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_RES, dir.data);
            dir.state := DIR_SM_DA;
          endif;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_SM_DA:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case PUTX:
          -- XXX: Copy data to memory.
          dir.data := msg.data;
          Send(PUT_ACK, msg.src, LLCache, DirMem, UNDEFINED, VC_UNB, UNDEFINED);
          dir.state := DIR_MI;

        case DATA_ACK:
          dir.state := DIR_M;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_SM_U_IA:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case INV_ACK:
          dir.need_acks := dir.need_acks - 1;
          if dir.need_acks = 0 then
            Send(UPGRADE_ACK, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_RES, UNDEFINED);
            dir.state := DIR_SM_DA;
          endif;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_M:
      Assert (IsUndefined(dir.owner) = false) "No owner, but line is in M";

      switch event
        case GETS:
          Send(DOWNGRADE, dir.owner, LLCache, DirMem, UNDEFINED, VC_REQ, UNDEFINED);
          AddToSharersList(msg.src);
          AddToSharersList(dir.owner);
          -- Use owner field as temporary storage for who to send to.
          dir.owner := msg.src;
          dir.state := DIR_MS2;

        case GETX:
          Send(INV, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_REQ, UNDEFINED);
          undefine dir.sharers;
          dir.owner := msg.src;
          dir.state := DIR_MM_P;

        case UPGRADE:
          Send(INV, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_REQ, UNDEFINED);
          undefine dir.sharers;
          dir.owner := msg.src;
          dir.state := DIR_MM_P;

        case PUTX:
          -- XXX: Copy data to memory
          dir.data := msg.data;
          Send(PUT_ACK, msg.src, LLCache, DirMem, UNDEFINED, VC_UNB, UNDEFINED);
          undefine dir.sharers;
          undefine dir.owner;
          dir.state := DIR_I;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_MM_P:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case PUTX:
          -- XXX: Do *not* copy data to memory, but forward on to new owner.
          Send(DATA, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_RES, msg.data);
          dir.state := DIR_MM_DA;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_MM_DA:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case PUTX:
          -- XXX: Copy data to memory.
          dir.data := msg.data;
          Send(PUT_ACK, msg.src, LLCache, DirMem, UNDEFINED, VC_UNB, UNDEFINED);
          dir.state := DIR_MI;

        case DATA_ACK:
          dir.state := DIR_M;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_MS2:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case DOWNGRADE_ACK:
          dir.state := DIR_MS1;

        case PUTX:
          -- XXX: Copy data to memory
          dir.data := msg.data;
          dir.state := DIR_MS1;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_MS1:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case DOWNGRADE_ACK:
          Send(DATA, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_RES, dir.data);
          Send(PUT_ACK, msg.src, LLCache, DirMem, UNDEFINED, VC_UNB, UNDEFINED);
          undefine dir.owner;
          dir.state := DIR_S;

        case PUTX:
          -- XXX: Copy data to memory
          dir.data := msg.data;
          Send(DATA, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_RES, dir.data);
          Send(PUT_ACK, msg.src, LLCache, DirMem, UNDEFINED, VC_UNB, UNDEFINED);
          undefine dir.owner;
          dir.state := DIR_S;

        else
          ErrorUnhandledMsg();
      endswitch;

    case DIR_MI:
      switch event
        case GETS:
          return false;

        case GETX:
          return false;

        case UPGRADE:
          return false;

        case PUTX:
          -- XXX: Copy data to memory
          dir.data := msg.data;
          undefine dir.sharers;
          undefine dir.owner;
          dir.state := DIR_I;

        case DATA_ACK:
          undefine dir.sharers;
          undefine dir.owner;
          dir.state := DIR_I;

        case INV_ACK:
          undefine dir.sharers;
          undefine dir.owner;
          dir.state := DIR_I;

        else
          ErrorUnhandledMsg();
      endswitch;

    else
      ErrorUnhandledState();
  endswitch;

  return true;
end;

-- }}}

--------------------------------------------------------------------------------
-- DRAMCache functions {{{
--------------------------------------------------------------------------------

function DRAMCacheReceive(msg:Message; s:Socket) : boolean;
var
  event:MessageType;
begin
  alias dc:sockets[s].dc do
    event := msg.mtype;

    switch dc.state
      case DC_I:
        switch event
          case GETS:
            Send(GETS, DirMem, UNDEFINED, s, DRAMCache, VC_REQ, UNDEFINED);
            dc.state := DC_IS;

          case GETX:
            Send(GETX, DirMem, UNDEFINED, s, DRAMCache, VC_REQ, UNDEFINED);
            dc.state := DC_IM;

          case UPGRADE:
            Send(UPGRADE, DirMem, UNDEFINED, s, DRAMCache, VC_REQ, UNDEFINED);
            dc.state := DC_SM_U;

          case PUTX:
            Send(PUTX, DirMem, UNDEFINED, s, DRAMCache, VC_RES, msg.data);
            --dc.state := DC_S; -- enabling this causes a SWMR violation!

          case INV:
            Send(INV, s, LLCache, msg.src, msg.src_lvl, msg.vc, UNDEFINED);

          else
            ErrorUnhandledMsg();
        endswitch;

      case DC_IS:
        switch event
          case PUTX:
            -- XXX: Do *not* copy data to D$.
            /*
            Race between L1 Replacement PUTX, Directory INV and a new request
            by L1. The directory will block until this request has arrived.
            */
            -- Forward
            Send(PUTX, DirMem, UNDEFINED, msg.src, msg.src_lvl, VC_RES, msg.data);

          case INV:
            Send(INV, s, LLCache, msg.src, msg.src_lvl, msg.vc, UNDEFINED);
            dc.state := DC_IS_I;

          case DATA:
            -- XXX: Put data in D$
            dc.data := msg.data;
            Send(DATA, s, LLCache, s, DRAMCache, VC_RES, dc.data);
            dc.state := DC_S;

          else
            ErrorUnhandledMsg();
        endswitch;

      case DC_IS_I:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, DRAMCache, VC_UNB, UNDEFINED);

          case DATA:
            -- XXX: No need to put data in D$
            Send(DATA, s, LLCache, s, DRAMCache, VC_RES, msg.data);
            dc.state := DC_I;

          else
            ErrorUnhandledMsg();
        endswitch;

      case DC_IM:
        switch event
          case PUTX:
            -- XXX: Do *not* copy data to D$.
            /*
            Race between L1 Replacement PUTX, Directory INV and a new request
            by L1. The directory will block until this request has arrived.
            */
            -- Forward
            Send(PUTX, DirMem, UNDEFINED, msg.src, msg.src_lvl, VC_RES, msg.data);

          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, DRAMCache, VC_UNB, UNDEFINED);

          case DATA:
            -- XXX: Put data in D$
            dc.data := msg.data;
            Send(DATA, s, LLCache, s, DRAMCache, VC_RES, dc.data);
            dc.state := DC_M;

          else
            ErrorUnhandledMsg();
        endswitch;

      case DC_S:
        switch event
          case GETS:
            Send(DATA, msg.src, msg.src_lvl, s, DRAMCache, VC_RES, dc.data);

          case GETX:
            --Send(UPGRADE, DirMem, UNDEFINED, s, DRAMCache, VC_REQ, UNDEFINED);
            Send(GETX, DirMem, UNDEFINED, s, DRAMCache, VC_REQ, UNDEFINED);
            dc.state := DC_SM;

          case UPGRADE:
            Send(UPGRADE, DirMem, UNDEFINED, s, DRAMCache, VC_REQ, UNDEFINED);
            dc.state := DC_SM_U;

          case INV:
            Send(INV, s, LLCache, msg.src, msg.src_lvl, msg.vc, UNDEFINED);
            dc.state := DC_I;
            undefine dc.data;

          else
            ErrorUnhandledMsg();
        endswitch;

      case DC_M:
        switch event
          case PUTX:
            -- XXX: Update data in D$
            dc.data := msg.data;
            Send(PUTX, DirMem, UNDEFINED, s, DRAMCache, VC_RES, dc.data);
            dc.state := DC_S;

          case INV:
            Send(INV, s, LLCache, msg.src, msg.src_lvl, msg.vc, UNDEFINED);
            dc.state := DC_I;
            undefine dc.data;

          else
            ErrorUnhandledMsg();
        endswitch;

      case DC_SM:
        switch event
          case INV:
            Send(INV, s, LLCache, msg.src, msg.src_lvl, msg.vc, UNDEFINED);
            dc.state := DC_IM;

          case DATA:
            -- XXX: Copy data
            dc.data := msg.data;
            Send(DATA, s, LLCache, s, DRAMCache, VC_RES, dc.data);
            dc.state := DC_M;

          --case UPGRADE_ACK:
          --  -- LLCache did not have data, but DRAMCache did.
          --  Send(DATA, s, LLCache, s, DRAMCache, VC_RES, dc.data);
          --  dc.state := DC_M;

          else
            ErrorUnhandledMsg();
        endswitch;

      case DC_SM_U:
        switch event
          case INV:
            Send(INV, s, LLCache, msg.src, msg.src_lvl, msg.vc, UNDEFINED);
            dc.state := DC_IM;

          case DATA:
            -- XXX: Copy data
            dc.data := msg.data;
            Send(DATA, s, LLCache, s, DRAMCache, VC_RES, dc.data);
            dc.state := DC_M;

          case UPGRADE_ACK:
            Send(UPGRADE_ACK, s, LLCache, s, DRAMCache, VC_RES, UNDEFINED);
            dc.state := DC_M;

          else
            ErrorUnhandledMsg();
        endswitch;

      else
        ErrorUnhandledState();
    endswitch;
  endalias;

  return true;
end;

-- }}}

--------------------------------------------------------------------------------
-- LLCache functions {{{
--------------------------------------------------------------------------------

procedure SatisfyInitialRequest(observed:Value; write:Value);
begin
  Assert (observed = aux_last_write) "[Safety] SC PER LOCATION";

  if !IsUndefined(write) then
    aux_last_write := write;
  endif;
end;

function LLCacheReceive(msg:Message; s:Socket) : boolean;
var
  event:MessageType;
begin
  alias l1c:sockets[s].l1c do
    event := msg.mtype;

    switch l1c.state
      case LLC_I:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);

          case PUT_ACK:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_IS:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_IS_I;

          case PUT_ACK:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_IS_I;

          case DATA:
            -- XXX: Copy data
            SatisfyInitialRequest(msg.data, UNDEFINED);
            l1c.data := msg.data;
            l1c.state := LLC_S;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_IS_I:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);

          case DATA:
/*
The SatisfyInitialRequest check here would fail as we are checking for SC PER
LOCATION in physical time, but is legal as we are only really interested in SC
PER LOCATION in logical time.

Lemma 1: SC PER LOCATION is not violated after Read in I state that is
  satisfied after DATA receipt in IS.
Proof: Via Murphi (see IS.DATA).   QED.

Lemma 2: SC PER LOCATION is not violated after Read in I state that is
  satisfied after DATA receipt in IS_I.
Proof: Let's assume that the DATA response message contains a stale value (i.e.
  not the latest or last seen value). This would imply that we may also violate
  SC PER LOCATION after a IS.DATA transition, as the only transition to IS_I is
  via an INV in IS that has overtaken an *already in-flight* DATA response.
  This, however, contradicts Lemma 1.   QED.
*/
            -- XXX: No need to copy data.
            --SatisfyInitialRequest(msg.data, UNDEFINED);
            l1c.state := LLC_I;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_IM:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);

          case PUT_ACK:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);

          case DOWNGRADE:
            Send(DOWNGRADE_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_IM_S;

          case DATA:
            SatisfyInitialRequest(msg.data, l1c.write);
            l1c.data := l1c.write;
            undefine l1c.write;
            Send(DATA_ACK, DirMem, UNDEFINED, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_M;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_IM_S:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);

          case DATA:
            -- XXX: Modify data, and then immediately send again with PUTX.
            SatisfyInitialRequest(msg.data, l1c.write);
            l1c.data := l1c.write;
            undefine l1c.write;
            Send(PUTX, s, DRAMCache, s, LLCache, VC_RES, l1c.data);
            l1c.state := LLC_MS;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_S:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_I;
            undefine l1c.data;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_SM:
        switch event
          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_IM;

          case DATA:
            SatisfyInitialRequest(msg.data, l1c.write);
            l1c.data := l1c.write;
            undefine l1c.write;
            Send(DATA_ACK, DirMem, UNDEFINED, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_M;

          case UPGRADE_ACK:
            SatisfyInitialRequest(l1c.data, l1c.write);
            l1c.data := l1c.write;
            undefine l1c.write;
            Send(DATA_ACK, DirMem, UNDEFINED, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_M;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_M:
        switch event
          case DOWNGRADE:
            Send(PUTX, s, DRAMCache, s, LLCache, VC_RES, l1c.data);
            Send(DOWNGRADE_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_MS;

          case INV:
            Send(PUTX, DirMem, UNDEFINED, s, LLCache, VC_RES, l1c.data);
            l1c.state := LLC_I;
            undefine l1c.data;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_MI:
        switch event
          case DOWNGRADE:
            Send(DOWNGRADE_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);

          case INV:
            l1c.state := LLC_I;

          case PUT_ACK:
            l1c.state := LLC_I;

          else
            ErrorUnhandledMsg();
        endswitch;

      case LLC_MS:
        switch event
          case PUT_ACK:
            l1c.state := LLC_S;

          case INV:
            Send(INV_ACK, msg.src, msg.src_lvl, s, LLCache, VC_UNB, UNDEFINED);
            l1c.state := LLC_MI;
            undefine l1c.data;

          else
            ErrorUnhandledMsg();
        endswitch;

      else
        ErrorUnhandledState();
    endswitch;
  endalias;

  return true;
end;

-- }}}

--------------------------------------------------------------------------------
-- Rules {{{
--------------------------------------------------------------------------------

-- Actions on Directory
rule "DIR_S.Replacement"
  (dir.state = DIR_S)
==>
  dir.state := DIR_I;
  undefine dir.sharers;
  undefine dir.owner;
endrule;

rule "DIR_M.Replacement"
  (dir.state = DIR_M)
==>
  Send(INV, dir.owner, DRAMCache, DirMem, UNDEFINED, VC_REQ, UNDEFINED);
  dir.state := DIR_MI;
endrule;


-- Actions on Sockets
ruleset s:Socket do
  alias l1c:sockets[s].l1c do
  alias dc:sockets[s].dc do

    -- LLCache -------------------------------------------------------
    rule "LLC_I.Read"
      (l1c.state = LLC_I)
    ==>
      Send(GETS, s, DRAMCache, s, LLCache, VC_REQ, UNDEFINED);
      l1c.state := LLC_IS;
    endrule;

    rule "LLC_S.Read"
      (l1c.state = LLC_S)
    ==>
      SatisfyInitialRequest(l1c.data, UNDEFINED);
    endrule;

    rule "LLC_M.Read"
      (l1c.state = LLC_M)
    ==>
      SatisfyInitialRequest(l1c.data, UNDEFINED);
    endrule;

    ruleset v:Value do
      rule "LLC_I.Write"
        (l1c.state = LLC_I)
      ==>
        Send(GETX, s, DRAMCache, s, LLCache, VC_REQ, UNDEFINED);
        l1c.state := LLC_IM;
        l1c.write := v;
      endrule;

      rule "LLC_S.Write"
        (l1c.state = LLC_S)
      ==>
        Send(UPGRADE, s, DRAMCache, s, LLCache, VC_REQ, UNDEFINED);
        l1c.state := LLC_SM;
        l1c.write := v;
      endrule;

      rule "LLC_M.Write"
        (l1c.state = LLC_M)
      ==>
        SatisfyInitialRequest(l1c.data, v);
        l1c.data := v;
      endrule;
    endruleset;

    rule "LLC_S.Replacement"
      (l1c.state = LLC_S)
    ==>
      l1c.state := LLC_I;
      undefine l1c.data;
    endrule;

    rule "LLC_M.Replacement"
      (l1c.state = LLC_M)
    ==>
      Send(PUTX, s, DRAMCache, s, LLCache, VC_REQ, l1c.data);
      l1c.state := LLC_MI;
      undefine l1c.data;
    endrule;

    -- DRAMCache --------------------------------------------------------
    rule "DC_S.Replacement"
      (dc.state = DC_S)
    ==>
      dc.state := DC_I;
      undefine dc.data;
    endrule;

    rule "DC_M.Replacement"
      (dc.state = DC_M)
    ==>
      dc.state := DC_I;
      undefine dc.data;
    endrule;

  endalias;
  endalias;
endruleset;

-- RECEIVE RULES -----------------------------------------------------
ruleset n:Node do
  choose midx:net[n] do
    alias chan:net[n] do
    alias msg:chan[midx] do

      rule "Network receive"
        !IsUndefined(msg.vc)
      ==>
        if IsMember(n, Directory) then
          if DirectoryReceive(msg) then
            MultiSetRemove(midx, chan);
          endif;
        else
          switch msg.dst_lvl
            case LLCache:
              if LLCacheReceive(msg, n) then
                MultiSetRemove(midx, chan);
              endif;

            case DRAMCache:
              if DRAMCacheReceive(msg, n) then
                MultiSetRemove(midx, chan);
              endif;

            else
              ErrorUnhandledMsg();
          endswitch;
        endif;
      endrule;

    endalias;
    endalias;
  endchoose;
endruleset;

-- }}}

--------------------------------------------------------------------------------
-- Startstate {{{
--------------------------------------------------------------------------------
ruleset v:Value do
  startstate
    -- Directory initialization
    dir.state := DIR_I;
    undefine dir.sharers;
    undefine dir.owner;
    undefine dir.need_acks;

    dir.data := v;
    aux_last_write := v;

    -- Processor initialization
    for i:Socket do
      sockets[i].l1c.state := LLC_I;
      sockets[i].dc.state := DC_I;
      undefine sockets[i].l1c.data;
      undefine sockets[i].dc.data;
    endfor;

    -- Network initialization
    undefine net;
  endstartstate;
endruleset;

-- }}}

--------------------------------------------------------------------------------
-- Invariants {{{
--------------------------------------------------------------------------------

-- Safety

invariant "[Safety] Single-Writer-Multiple-Reader (SWMR)"
  forall s1:Socket do
  forall s2:Socket do
    ( s1 != s2
    & sockets[s1].l1c.state = LLC_M )
    ->
    ( sockets[s2].l1c.state != LLC_M
    & sockets[s2].l1c.state != LLC_S )
  endforall
  endforall;

-- Model optimizations

invariant "[Model opt.] M or I implies empty sharers list"
  ( dir.state = DIR_M
  | dir.state = DIR_I )
  ->
  ( MultiSetCount(i:dir.sharers, true) = 0 );

invariant "[Model opt.] S or I implies undefined owner"
  ( dir.state = DIR_S
  | dir.state = DIR_I )
  ->
  ( IsUndefined(dir.owner) );

invariant "[Model opt.] No useless data in LLCache"
  forall s:Socket do
    ( sockets[s].l1c.state = LLC_I )
    ->
    ( IsUndefined(sockets[s].l1c.data) )
  endforall;

invariant "[Model opt.] No useless data in DRAMCache"
  forall s:Socket do
    ( sockets[s].dc.state = DC_I )
    ->
    ( IsUndefined(sockets[s].dc.data) )
  endforall;

invariant "[Model opt.] No useless destination level"
  forall n:Node do
    ( MultiSetCount(m:net[n],
      ( n = DirMem
      & !IsUndefined(net[n][m].dst_lvl) )
      ) = 0 )
  endforall;

-- }}}

-- vim: set ft=murphi shiftwidth=2 :
