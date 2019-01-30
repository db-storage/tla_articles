------------------ MODULE WriteThroughCache ------------------
EXTENDS Naturals, Sequences 
VARIABLES wmem, ctl, buf, cache, memQ 

CONSTANTS QLen,
          Proc,  
           Adr,  
           Val
ASSUME (QLen \in Nat) /\ (QLen > 0)
--------------------------------------------------------------
MReq == [op : {"Rd"}, adr: Adr] 
          \cup [op : {"Wr"}, adr: Adr, val : Val]

NoVal == CHOOSE v : v \notin Val
--------------------------------------------------------------
Init == /\ wmem \in [Adr->Val]
        /\ ctl = [p \in Proc |-> "rdy"] 
        /\ buf = [p \in Proc |-> NoVal] 
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal] ]
        /\ memQ = << >>  
 
TypeInvariant == 
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}] 
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]] 
  /\ memQ  \in Seq(Proc \X MReq) 

Coherence == \A p, q \in Proc, a \in Adr : 
                (NoVal \notin {cache[p][a], cache[q][a]})
                      => (cache[p][a]=cache[q][a]) 
--------------------------------------------------------------
Req(p) == /\ ctl[p] = "rdy" 
          /\ \E req \in  MReq :
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED <<cache, memQ, wmem>>  


Rsp(p) == /\ ctl[p] = "done"
          /\ ctl' = [ctl EXCEPT ![p]= "rdy"]
          /\ UNCHANGED <<cache, memQ, wmem, buf>> 
 

RdMiss(p) ==  /\ (ctl[p] = "busy") /\ (buf[p].op = "Rd") 
              /\ cache[p][buf[p].adr] = NoVal 
              /\ Len(memQ) < QLen
              /\ memQ' = Append(memQ, <<p, buf[p]>>)
              /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
              /\ UNCHANGED <<wmem, buf, cache>>

DoRd(p) == 
  /\ ctl[p] \in {"busy","waiting"} 
  /\ buf[p].op = "Rd" 
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<wmem, cache, memQ>> 

DoWr(p) == 
  LET r == buf[p]
  IN  /\ (ctl[p] = "busy") /\ (r.op = "Wr") 
      /\ Len(memQ) < QLen
      /\ cache' = [q \in Proc |-> 
                    IF (p=q)  \/  (cache[q][r.adr]#NoVal)
                      THEN [cache[q] EXCEPT ![r.adr] = r.val]
                      ELSE cache[q] ]
      /\ memQ' = Append(memQ, <<p, r>>)
      /\ buf' = [buf EXCEPT ![p] = NoVal]
      /\ ctl' = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<wmem>> 

(* f is a function,  f[0 .. Len(memQ)] -> (Map[Adr] -> Val)                 *)
(* vmem == f[Len(memQ)], the LAST ITEM in f,  it's a map: Map[Adr] -> Val   *)
(* So vmem, is  wmem + all writes in memQ                                   *)
(* f[0] =  wmem                                                             *)
(* For i > 0,                                                               *)
(*     IF memQ[i] is a "Rd", skip it, so f[i] = f[i-1]                      *)
(*     ELSE f[i] = f[i-1] EXECPT f[i][memQ[i][2].adr] =memQ[i][2].val       *)

vmem  ==  
  LET f[i \in 0 .. Len(memQ)] == 
        IF i=0 THEN wmem
               ELSE IF memQ[i][2].op = "Rd"
                      THEN f[i-1]
                      ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] =
                                              memQ[i][2].val]
  IN f[Len(memQ)] 

MemQWr == LET r == Head(memQ)[2] 
          IN  /\ (memQ # << >>)  /\   (r.op = "Wr") 
              /\ wmem' = [wmem EXCEPT ![r.adr] = r.val] 
              /\ memQ' = Tail(memQ) 
              /\ UNCHANGED <<buf, ctl, cache>> 

MemQRd == 
  LET p == Head(memQ)[1] 
      r == Head(memQ)[2] 
  IN  /\ (memQ # << >> ) /\ (r.op = "Rd")
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ UNCHANGED <<wmem, buf, ctl>>  

Evict(p,a) == /\ (ctl[p] = "waiting") => (buf[p].adr # a) 
              /\ cache' = [cache EXCEPT ![p][a] = NoVal]
              /\ UNCHANGED <<wmem, buf, ctl, memQ>> 

Next == \/ \E p\in Proc : \/ Req(p) \/ Rsp(p) 
                          \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p) 
                          \/ \E a \in Adr : Evict(p, a)
        \/ MemQWr \/ MemQRd    

Spec == 
  Init /\ [][Next]_<<wmem, buf, ctl, cache, memQ>>

==============================================================