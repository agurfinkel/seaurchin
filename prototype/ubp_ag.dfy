datatype Tag = Unique(t: nat) | SharedRO(t: nat) | SharedRW(t: nat) 
datatype MaybePointer = None | Some(p:Pointer)

class State {
   var counter: nat; // used to generate new id

   // main memory
   var mem: array<int>;

   // the following configurations are possible
   // ptrOnStack == None, tracked_tag == Unique(0) 
   //     ==> no pointer is tracked
   // ptrOnStack == Some(p), tracked_tag == p.tag
   //     ==> pointer p is tracked, currently on stack, maybe top?
   // ptrOnStack == None, tracked_tag == Unique(t), t > 0
   //     ==> pointer p is tracked, but was removed from the stack, 
  //          using it is an error
   var ptrOnStack : MaybePointer;
   var tracked_tag : Tag;
   
   constructor() 
   {
     this.counter := 1;
     this.ptrOnStack := None;
     this.tracked_tag := Unique(0);
   }
   method newId() returns (ret: nat) 
   modifies this;
   {
     counter := counter + 1;
     ret := counter;
   }
   
   method push(p: Pointer)
   {
     if (*) 
     {
       this.tracked_tag := p.tag;
       this.ptrOnStack := Some(p);
     }
   }

   method use(p: Pointer) 
   requires p.tag == this.tracked_tag ==> this.ptrOnStack != None
   {
     // if using a pointer with tracked_tag, and the pointer is 
     // not in the stack, then this is an error
     // all other cases are ok
     if (p.tag == this.tracked_tag) 
     {
       assert this.ptrOnStack != None;
     } 
     else
     {
       // if tracked pointer is on stack, and its predecessor 
       // is being used, then the tracked pointer is removed 
       // from the stack
       match this.ptrOnStack
       case None => 
       case Some(ptr) => 
           assert ptr.tag == this.tracked_tag;
           assert p.tag != ptr.tag;
           if (ptr.ancestor == Some(p)) 
           {
             this.ptrOnStack := None;
           }
     }
   }

   predicate isWritable(p: Pointer)
   requires p.valid(this);
   reads this, p;
   { 
      match p.tag
      case Unique(t, c)  => p.tag in ancestors[tagmem[p.addr]]
      case SharedRW(t, c) =>  p.tag in ancestors[tagmem[p.addr]]
      case _ => false
   }
   
   method write(p: Pointer, v: int)
     requires p.valid(this) && isWritable(p);
     modifies mem, tagmem;
   {
     match p.tag
     case Unique(t, c) =>
       use1(p);
       mem[p.addr] := v;
     case SharedRW(t, c) =>
        tagmem[p.addr] := p.tag; // update the top
         mem[p.addr] := v;
   }
   
 method use1(p: Pointer) 
 requires p.valid(this);
{
  match p.tag
  case Unique(t, c) =>  
    // Rule (USE -1 ) 
    // requires Unique(t) is in the stack
    // p becomes the top
    tagmem[p.addr] := p.tag; 
}

method use2(p: Pointer)
requires p.valid(this);
{
  if (raw[p.addr]) { // Pointer(l, Bot)
    // pop up anything above SharedRWBot
    tagmem[p.addr] := SharedRWBot;
  } else{
    match p.tag
    case Unique(t, c) => // Pointer(l, t)
    // pop up anything above Pointer(l, t)
    tagmem[p.addr] := p.tag;
  }
}
   
   method read(p: Pointer) returns (r: int)
   requires p.valid(this);
   {
     r := mem[p.addr];
     match p.tag
     case Unique(t, c) =>
        use1(p);
     case SharedRO(t, c) =>
      // nothing to do
     case SharedRW(t, c) => 
      // ?
     
   }
} 
   

class Pointer 
{
  // -- address of this pointer
  var addr: nat;
  // -- the tag
  var tag: Tag;
  // -- immediate predecessor, or None if the pointer owns its memory
  var pred: MaybePointer;
  // -- some ancestor of the pointer
  // -- this is the prophecy of an intersting ancesstor
  var ancestor: MaybePointer;
  
  predicate valid(s: State)
  {
    true
  }
  
  constructor(addr: nat, tag: Tag, pred: Pointer, ances: Pointer) 
  {
    this.addr := addr;
    this.tag := tag;
    this.pred := Some(pred);
    this.ancestor := match ances 
                    case None => Some(pred)
                    case Some(p) => ances;
  }


  constructor(addr: nat, s: State) 
  {
    this.addr := addr;
    var id := s.newId();
    this.tag := Unique(id);
    this.pred := None;
    this.ancestor := None;
  }

  method mut_borrow(s: State) returns (p: Pointer) 
  {
    s.use(this);
    var ancestor := this;
    if (*) 
    {
      match this.ancestor
      case None => 
      case Some(t) => ancestor := t;
    }
    var id := s.newId();
    var np := new Pointer(p.addr, Unique(id), this, ancestor);
    s.push(np);
    return np;
  }

  method borrow(s: State) returns (p: Pointer) 
  {

    return new Pointer(this.addr, SharedRO(s.newId()));
  }

  method raw(s: State) returns (p: Pointer) 
  {
    return new Pointer(this.addr, SharedRW(s.newId()));
  }

  method write(val: int, s: State) 
  {
    this.use(s);

  }

  method read(s: State) returns (val: int)
  {
    this.use(s);

  }

  method use(s: State) 
  {
    s.use(this);
  }


}

method createOwner(addr: nat, s: State)  returns(ret: Pointer) 
modifies s;
{
   var newID := s.generateID();
   var new_tag := Unique(newID, 1);
   ret := new Pointer(addr, new_tag);
   s.ancestors := s.ancestors[new_tag := {new_tag}];
   s.predecessor := s.predecessor[new_tag := new_tag];
   s.raw[addr] := false;
}

method createMutableRef(p: Pointer, s: State) returns(ret: Pointer)
requires p.valid(s);
modifies s;
{
  var newID := s.generateID();
  
  var predecessor_of_top := s.predecessor[p.tag];
  var ancestors_of_top := s.ancestors[p.tag];
  
  match p.tag
    case Unique(t, c) =>
        /*
            let x = & mut p;
            1. it is considered as a use of p
            2. generate a fresh tag for the new reference x, i.e., Unique(t', c)
            3. record Unique(t', c)'s predecessor
            4. record Unique(t',c)'s ancestors
            5. push Unique(t', c) to the stack
        */
       var top := s.tagmem[p.addr];
       var newtag := Unique(newID, c);
       s.use1(p);
       ret := new Pointer(p.addr, newtag);
       s.predecessor := s.predecessor[newtag := predecessor_of_top];
       s.ancestors := s.ancestors[newtag := ancestors_of_top + {newtag}];
       s.tagmem[p.addr] := newtag;
    case Raw =>
       // todo
}

/*
Rule (NEW-SHARE-REF-1)
*/
method createShareRef(p: Pointer, s: State) returns(ret: Pointer)
requires p.valid(s);
modifies s;
{
  var newID := s.generateID();
  var predecessor_of_top := s.predecessor[p.tag];
  var ancestors_of_top := s.ancestors[p.tag];
  
  /*
  1. consider a read access to p
  2. generate a fresh tag for the new reference x, i.e., SharedRO(t', c)
  3. record SharedRO(t', c)'s predecessor
  4. record SharedRO(t', c)'s ancestors
  5. update lastread as SharedRO(t', c)
  6. push SharedRO(t', c) to the stack
  */
  readPointer(p, s);
  var newtag := SharedRO(newID, 1);
  ret := new Pointer(p.addr, newtag);
  s.predecessor := s.predecessor[newtag := predecessor_of_top];
  s.ancestors := s.ancestors[newtag := ancestors_of_top + {newtag}];
  s.lastread[p.addr] := newtag;
  s.tagmem[p.addr] := newtag;
}

// Rule READ-1
// p could be Unique(t, c), SharedRO(t, c), SharedRW(t, c)
method readPointer(p: Pointer, s: State)
requires p.valid(s) ;
modifies s, s.tagmem;
{
  // pop items off the stack until all the items above the item 
  // with tag t are SharedRO(t, c)
  s.tagmem[p.addr] := s.lastread[p.addr];
}

/*
Raw pointers can only be created from Unique(t)
let raw_pointer = &mut p as *mut i32;
*/
method createMutableRawRef(p: Pointer, s: State) returns(ret: Pointer)
requires p.valid(s);
modifies s;
{
  var newID := s.generateID();
  var top := s.tagmem[p.addr];
  var predecessor_of_top := s.predecessor[p.tag];
  var ancestors_of_top := s.ancestors[p.tag];
  
  match p.tag
  case ShareRWBot =>
      /*
      1. a use of p
      2. generate new pointer
      3. record new tag's predecessor
      4. record new tag's ancestors
      5. push ShareRW(BOT) on the top
      */
      var newtag := Unique(newID, 1);
      s.use2(p);
      var ret := new Pointer(p.addr, newtag);
      s.predecessor := s.predecessor[newtag := top];
      s.ancestors := s.ancestors[newtag := s.ancestors[top] + {newtag}];
      s.tagmem[p.addr] := newtag;
   case Unique(t, c) =>
      /*
      Rule (NEW-MUTABLE-RAW-1)
      1. a use of p (USE-2)
      2. generate new pointer
      3. record new tag's predecessor
      4. record new tag's ancestors
      5. push ShareRW(BOT) on the top
      6. mark the addr as raw
      */
      var newtag := SharedRWBot;
      s.use2(p);
      var ret := new Pointer(p.addr, newtag);
      s.predecessor := s.predecessor[newtag := predecessor_of_top];
      s.ancestors := s.ancestors[newtag := ancestors_of_top + {newtag}];
      s.tagmem[p.addr] := newtag;
      s.raw[p.addr] := true;
}
