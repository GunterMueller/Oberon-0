(* OSP.m
 * From N. Wirth: Compiler Construction
 * Revised 2005 edition from www.ethoberon.ethz.ch/WirthPubl/CBEAll.pdf
 * Ported to Oxford Oberon-2 Compiler 2.9.7 for Windows
 * 22.07.2016 TSS
 * Changes from the original:
 * - Replaced text I/O with console I/O using module Out
 * - Text to compile is specified as a command-line argument
 *   that is accessed via module Args
 * - Load/Execute not implemented
 * - Error messages via OSS.Mark() are a little more kind
 * - Procedure declarations(): removed unused local L
 * - Procedure Module(): differences due to using Files instead of Texts
 * - Procedure Compile(): takes the file name as argument
 * - Module body code: run the compile immediately
 * - Some "debugging printfs" are still strewn about the code
 *)

MODULE OSP;

   IMPORT Out, Args, OSS, OSG;

   CONST
      WordSize = 4;
      maxFileChars = 20;
      
   VAR
      sym: INTEGER;
      topScope, universe: OSG.Object;
      guard: OSG.Object;
      fileName: ARRAY maxFileChars OF CHAR;
      
   PROCEDURE NewObj(VAR obj: OSG.Object; class:INTEGER);
      VAR new, x: OSG.Object;
   BEGIN
      x := topScope;
      guard.name := OSS.id;
      WHILE x.next.name # OSS.id DO
         x := x.next
      END;
      IF x.next = guard THEN
         NEW(new);
         new.name := OSS.id;
         new.class := class;
         new.next := guard;
         x.next := new;
         obj := new
      ELSE
         obj := x.next;
         OSS.Mark("Symbol already defined")
      END
   END NewObj;
   
   PROCEDURE find(VAR obj: OSG.Object);
      VAR s, x: OSG.Object;
   BEGIN
      s := topScope;
      guard.name := OSS.id;
      LOOP
         x := s.next;
         WHILE x.name # OSS.id DO
            x := x.next
         END;
         IF x # guard THEN
            obj := x;
            EXIT
         END;
         IF s = universe THEN
            obj := x;
            OSS.Mark("Symbol not defined");
            EXIT
         END;
         s := s.dsc
      END
   END find;
   
   PROCEDURE FindField(VAR obj: OSG.Object; list: OSG.Object);
   BEGIN
      guard.name := OSS.id;
      WHILE list.name # OSS.id DO
         list := list.next
      END;
      obj := list
   END FindField;
   
   PROCEDURE IsParam(obj: OSG.Object):BOOLEAN;
   BEGIN
      RETURN (obj.class = OSG.Par) OR (obj.class = OSG.Var) & (obj.val > 0)
   END IsParam;
   
   PROCEDURE OpenScope;
      VAR s: OSG.Object;
   BEGIN
      NEW(s);
      s.class := OSG.Head;
      s.dsc := topScope;
      s.next := guard;
      topScope := s
   END OpenScope;
   
   PROCEDURE CloseScope;
   BEGIN
      topScope := topScope.dsc
   END CloseScope;
   
   (* Parser *)
   PROCEDURE^ expression(VAR x:OSG.Item);
   
   PROCEDURE selector(VAR x: OSG.Item);
      VAR y: OSG.Item; obj: OSG.Object;
   BEGIN
      WHILE (sym = OSS.lbrak) OR (sym = OSS.period) DO
         IF sym = OSS.lbrak THEN
            OSS.Get(sym);
            expression(y);
            IF x.type.form = OSG.Array THEN
               OSG.Index(x,y)
            ELSE
               OSS.Mark("Selector: not an array")
            END;
            IF sym = OSS.rbrak THEN
               OSS.Get(sym)
            ELSE
               OSS.Mark("Selector: right bracket expected")
            END
         ELSE
            OSS.Get(sym);
            IF sym = OSS.ident THEN
               IF x.type.form = OSG.Record THEN
                  FindField(obj, x.type.fields);
                  OSS.Get(sym);
                  IF obj # guard THEN
                     OSG.Field(x, obj)
                  ELSE
                     OSS.Mark("Selector: undefined record field")
                  END
               ELSE
                  OSS.Mark("Selector: Not a record")
               END
            ELSE
               OSS.Mark("Selector: Identifier expected")
            END
         END
      END
   END selector;
   
   PROCEDURE factor(VAR x: OSG.Item);
      VAR obj: OSG.Object;
   BEGIN
      (* sync *)
      IF sym < OSS.lparen THEN
         OSS.Mark("Factor: Identifier expected");
         REPEAT
            OSS.Get(sym)
         UNTIL sym >= OSS.lparen
      END;
      IF sym = OSS.ident THEN
         find(obj);
         OSS.Get(sym);
         OSG.MakeItem(x, obj);
         selector(x)
      ELSIF sym = OSS.number THEN
         OSG.MakeConstItem(x, OSG.intType, OSS.val);
         OSS.Get(sym)
      ELSIF sym = OSS.lparen THEN
         OSS.Get(sym);
         expression(x);
         IF sym = OSS.rparen THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("Factor: ) expected")
         END
      ELSIF sym = OSS.not THEN
         OSS.Get(sym);
         factor(x);
         OSG.Op1(OSS.not, x)
      ELSE
         OSS.Mark("Factor: factor expected.");
         OSG.MakeItem(x, guard)
      END
   END factor;
   
   PROCEDURE term(VAR x: OSG.Item);
      VAR y: OSG.Item; op: INTEGER;
   BEGIN
      factor(x);
      WHILE (sym >= OSS.times) & (sym <= OSS.and) DO
         op := sym;
         OSS.Get(sym);
         IF op = OSS.and THEN
            OSG.Op1(op, x)
         END;
         factor(y);
         OSG.Op2(op, x, y)
      END
   END term;
   
   PROCEDURE SimpleExpression(VAR x: OSG.Item);
      VAR y: OSG.Item; op:INTEGER;
   BEGIN
      IF sym = OSS.plus THEN
         OSS.Get(sym);
         term(x)
      ELSIF sym = OSS.minus THEN
         OSS.Get(sym);
         term(x);
         OSG.Op1(OSS.minus, x)
      ELSE
         term(x)
      END;
      WHILE (sym >= OSS.plus) & (sym <= OSS.or) DO
         op := sym;
         OSS.Get(sym);
         IF op = OSS.or THEN
            OSG.Op1(op, x)
         END;
         term(y);
         OSG.Op2(op, x, y)
      END
   END SimpleExpression;
   
   PROCEDURE expression(VAR x: OSG.Item);
      VAR y: OSG.Item; op: INTEGER;
   BEGIN
      SimpleExpression(x);
      IF (sym >= OSS.eql) & (sym <= OSS.gtr) THEN
         op := sym;
         OSS.Get(sym);
         SimpleExpression(y);
         OSG.Relation(op, x, y)
      END
   END expression;
   
   PROCEDURE parameter(VAR fp: OSG.Object);
      VAR x: OSG.Item;
   BEGIN
      expression(x);
      IF IsParam(fp) THEN
         OSG.Parameter(x, fp.type, fp.class);
         fp := fp.next
      ELSE
         OSS.Mark("Parameter: too many procedure parameters")
      END
   END parameter;
   
   PROCEDURE StatSequence;
      VAR
         par, obj: OSG.Object;
         x, y: OSG.Item;
         L: LONGINT;
         
      PROCEDURE param(VAR x: OSG.Item);
      BEGIN
         IF sym = OSS.lparen THEN 
            OSS.Get(sym)
         ELSE
            OSS.Mark("Param: ( expected")
         END;
         expression(x);
         IF sym = OSS.rparen THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("Param: ) expected")
         END
      END param;
      
   BEGIN (*StatSequence *)
      Out.String("StatSequence"); Out.Ln;
      LOOP
         (* sync *)
         obj := guard;
         IF sym < OSS.ident THEN
            OSS.Mark("StatSequence: statement expected");
            REPEAT
               OSS.Get(sym)
            UNTIL sym >= OSS.ident
         END;
         IF sym = OSS.ident THEN
            (* Assignment statement *)
            find(obj);
            OSS.Get(sym);
            OSG.MakeItem(x, obj);
            selector(x);
            IF sym = OSS.becomes THEN
               OSS.Get(sym);
               expression(y);
               Out.String("Assignment"); Out.Ln;
               OSG.Store(x, y)
            ELSIF sym = OSS.eql THEN
               OSS.Mark("StatSequence: := expected, = found");
               OSS.Get(sym);
               expression(y)
            ELSIF x.mode = OSG.Proc THEN
               par := obj.dsc;
               IF sym = OSS.lparen THEN
                  OSS.Get(sym);
                  IF sym = OSS.rparen THEN
                     OSS.Get(sym)
                  ELSE
                     LOOP
                        parameter(par);
                        IF sym = OSS.comma THEN
                           OSS.Get(sym)
                        ELSIF sym = OSS.rparen THEN
                           OSS.Get(sym);
                           EXIT
                        ELSIF sym >= OSS.semicolon THEN
                           EXIT
                        ELSE
                           OSS.Mark("StatSequence: ) or , or ; expected in procedure declaration")
                        END
                     END
                  END
               END;
               IF obj.val < 0 THEN
                  OSS.Mark("StatSequence: Forward call")
               ELSIF ~IsParam(par) THEN
                  OSG.Call(x)
               ELSE
                  OSS.Mark("StatSequence: too few parameters")
               END
            ELSIF x.mode = OSG.SProc THEN
               IF obj.val <= 3 THEN
                  param(y)
               END;
               OSG.IOCall(x, y)
            ELSIF obj.class = OSG.Typ THEN
               OSS.Mark("StatSequence: illegal assignment")
            ELSE
               OSS.Mark("StatSequence: statement expected")
            END
         ELSIF sym = OSS.if THEN
            (* IF-ELSIF-ELSE statement *)
            OSS.Get(sym);
            expression(x);
            OSG.CJump(x);
            IF sym = OSS.then THEN
               OSS.Get(sym)
            ELSE
               OSS.Mark("StatSequence: IF-clause: THEN expected")
            END;
            StatSequence;
            L := 0;
            WHILE sym = OSS.elsif DO
               OSS.Get(sym);
               OSG.FJump(L);
               OSG.FixLink(x.a);
               expression(x);
               OSG.CJump(x);
               IF sym = OSS.then THEN
                  OSS.Get(sym)
               ELSE
                  OSS.Mark("StatSequence: ELSIF-clause: THEN expected")
               END;
               StatSequence
            END;
            IF sym = OSS.else THEN
               OSS.Get(sym);
               OSG.FJump(L);
               OSG.FixLink(x.a);
               StatSequence
            ELSE
               OSG.FixLink(x.a)
            END;
            OSG.FixLink(L);
            IF sym = OSS.end THEN 
               OSS.Get(sym)
            ELSE
               OSS.Mark("StatSequence: IF statement: END expected")
            END
         ELSIF sym = OSS.while THEN
            (* WHILE statement *)
            OSS.Get(sym);
            L := OSG.pc;
            expression(x);
            OSG.CJump(x);
            IF sym = OSS.do THEN
               OSS.Get(sym)
            ELSE
               OSS.Mark("StatSequence: WHILE statement: DO expected after expression")
            END;
            StatSequence;
            OSG.BJump(L);
            OSG.FixLink(x.a);
            IF sym = OSS.end THEN
               OSS.Get(sym)
            ELSE
               OSS.Mark("StatSequence: WHILE statement: END expected after body")
            END
         END;
         IF sym = OSS.semicolon THEN
            OSS.Get(sym)
         ELSIF (sym >= OSS.semicolon) & (sym < OSS.if) OR (sym >= OSS.array) THEN
            EXIT
         ELSE
            OSS.Mark("StatSequence: ; expected")
         END
      END
   END StatSequence;
               
   PROCEDURE IdentList(class: INTEGER; VAR first: OSG.Object);
      VAR obj: OSG.Object;
   BEGIN
      IF sym = OSS.ident THEN
         NewObj(first, class);
         OSS.Get(sym);
         WHILE sym = OSS.comma DO
            OSS.Get(sym);
            IF sym = OSS.ident THEN
               NewObj(obj, class);
               OSS.Get(sym)
            ELSE
               OSS.Mark("IdentList: identifier expected")
            END
         END;
         IF sym = OSS.colon THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("IdentList: colon expected")
         END
      END
   END IdentList;
   
   PROCEDURE Type(VAR type: OSG.Type);
      VAR
         obj, first: OSG.Object;
         x: OSG.Item;
         tp: OSG.Type;
   BEGIN
      type := OSG.intType;
      (* sync *)
      IF (sym # OSS.ident) & (sym < OSS.array) THEN
         OSS.Mark("Type: type expected");
         REPEAT
            OSS.Get(sym)
         UNTIL (sym = OSS.ident) OR (sym >= OSS.array)
      END;
      IF sym = OSS.ident THEN
         find(obj);
         OSS.Get(sym);
         IF obj.class = OSG.Typ THEN
            type := obj.type
         ELSE
            OSS.Mark("Type: Not a recognized type")
         END
      ELSIF sym = OSS.array THEN
         OSS.Get(sym);
         expression(x);
         IF (x.mode # OSG.Const) OR (x.a < 0) THEN
            OSS.Mark("Type: array index must be constant and positive")
         END;
         IF sym = OSS.of THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("Type: OF expected after size expression")
         END;
         Type(tp);
         NEW(type);
         type.form := OSG.Array; 
         type.base := tp;
         type.len := SHORT(x.a);
         type.size := type.len*tp.size
      ELSIF sym = OSS.record THEN
         OSS.Get(sym);
         NEW(type);
         type.form := OSG.Record;
         type.size := 0;
         OpenScope;
         LOOP
            IF sym = OSS.ident THEN
               IdentList(OSG.Fld, first);
               Type(tp);
               obj := first;
               WHILE obj # guard DO
                  obj.type := tp;
                  obj.val := type.size;
                  INC(type.size, obj.type.size);
                  obj := obj.next
               END
            END;
            IF sym = OSS.semicolon THEN
               OSS.Get(sym)
            ELSIF sym = OSS.ident THEN
               OSS.Mark("Type: ; expected")
            ELSE
               EXIT
            END
         END;
         type.fields := topScope.next;
         CloseScope;
         IF sym = OSS.end THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("Type: END expected")
         END
      ELSE
         OSS.Mark("Type: identifier expected")
      END
   END Type;
                        
   PROCEDURE declarations(VAR varsize: LONGINT);
      VAR
         obj, first: OSG.Object;
         x: OSG.Item;
         tp: OSG.Type;
   BEGIN
      (* sync *)
      IF (sym < OSS.const) & (sym # OSS.end) THEN
         OSS.Mark("Declarations: declaration expected");
         REPEAT
            OSS.Get(sym)
         UNTIL (sym >= OSS.const) OR (sym = OSS.end)
      END;
      LOOP
         IF sym = OSS.const THEN
            OSS.Get(sym);
            WHILE sym = OSS.ident DO
               NewObj(obj, OSG.Const);
               OSS.Get(sym);
               IF sym = OSS.eql THEN
                  OSS.Get(sym)
               ELSE
                  OSS.Mark("Declarations: CONST: = expected")
               END;
               expression(x);
               IF x.mode = OSG.Const THEN
                  obj.val := x.a;
                  obj.type := x.type
               ELSE
                  OSS.Mark("Declarations: CONST: expression not constant")
               END;
               IF sym = OSS.semicolon THEN
                  OSS.Get(sym);
                  (* DEBUG *)
                  Out.String("CONST declaration found: ");
                  Out.String(obj.name);
                  Out.LongInt(obj.val, 4); Out.Ln
               ELSE
                  OSS.Mark("Declarations: CONST: ; expected")
               END
            END
         END;
         IF sym = OSS.type THEN
            OSS.Get(sym);
            WHILE sym = OSS.ident DO
               NewObj(obj, OSG.Typ);
               OSS.Get(sym);
               IF sym = OSS.eql THEN
                  OSS.Get(sym)
               ELSE
                  OSS.Mark("Declarations: TYPE: = expected");
               END;
               Type(obj.type);
               IF sym = OSS.semicolon THEN
                  OSS.Get(sym);
                  (* DEBUG *)
                  Out.String("TYPE declaration found: ");
                  Out.String(obj.name); Out.Ln;
               ELSE
                  OSS.Mark("Declarations: TYPE: ; expected")
               END
            END
         END;
         IF sym = OSS.var THEN
            OSS.Get(sym);
            WHILE sym = OSS.ident DO
               IdentList(OSG.Var, first);
               Type(tp);
               obj := first;
               WHILE obj # guard DO
                  obj.type := tp;
                  obj.lev := OSG.curlev;
                  varsize := varsize + obj.type.size;
                  obj.val := -varsize;
                  obj := obj.next
               END;
               IF sym = OSS.semicolon THEN
                  OSS.Get(sym);
                  (* DEBUG *)
                  Out.String("VAR declaration found: ");
                  Out.String(first.name); Out.Ln;
               ELSE
                  OSS.Mark("Declarations: VAR: ; expected")
               END
            END
         END;
         IF (sym >= OSS.const) & (sym <= OSS.var) THEN
            OSS.Mark("Declarations: wrong sequence of declarations")
         ELSE
            EXIT
         END
      END
   END declarations;
   
   PROCEDURE ProcedureDecl;
      CONST marksize = 8;
      VAR
         proc, obj: OSG.Object;
         procid: OSS.Ident;
         locblksize, parblksize: LONGINT;
      
      PROCEDURE FPSection;
         VAR
            obj, first: OSG.Object;
            tp: OSG.Type;
            parsize: LONGINT;
      BEGIN
         IF sym = OSS.var THEN
            OSS.Get(sym);
            IdentList(OSG.Par, first)
         ELSE
            IdentList(OSG.Var, first)
         END;
         IF sym = OSS.ident THEN
            find(obj);
            OSS.Get(sym);
            IF obj.class = OSG.Typ THEN
               tp := obj.type
            ELSE
               OSS.Mark("FPSection: Identifier expected");
               tp := OSG.intType
            END
         ELSE
            OSS.Mark("FPSection: Identifier expected");
            tp := OSG.intType
         END;
         IF first.class = OSG.Var THEN
            parsize := tp.size;
            IF tp.form >= OSG.Array THEN
               OSS.Mark("FPSection: no struct params")
            END;
         ELSE
            parsize := WordSize
         END;
         obj := first;
         WHILE obj # guard DO
            obj.type := tp;
            INC(parblksize, parsize);
            obj := obj.next
         END
      END FPSection;
   
   BEGIN (* ProcedureDecl *)
      OSS.Get(sym);
      IF sym = OSS.ident THEN
         procid := OSS.id;
         NewObj(proc, OSG.Proc);
         OSS.Get(sym);
         parblksize := marksize;
         OSG.IncLevel(1);
         OpenScope;
         proc.val := -1;
         IF sym = OSS.lparen THEN
            OSS.Get(sym);
            IF sym = OSS.rparen THEN
               OSS.Get(sym)
            ELSE
               FPSection;
               WHILE sym = OSS.semicolon DO
                  OSS.Get(sym);
                  FPSection
               END;
               IF sym = OSS.rparen THEN
                  OSS.Get(sym)
               ELSE
                  OSS.Mark("ProcedureDecl: ) expected")
               END
            END
         ELSIF OSG.curlev = 1 THEN
            OSG.EnterCmd(procid)
         END;
         obj := topScope.next;
         locblksize := parblksize;
         WHILE obj # guard DO
            obj.lev := OSG.curlev;
            IF obj.class = OSG.Par THEN
               DEC(locblksize, WordSize)
            ELSE
               obj.val := locblksize;
               obj := obj.next
            END
         END;
         proc.dsc := topScope.next;
         IF sym = OSS.semicolon THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("ProcedureDecl: ; expected")
         END;
         locblksize := 0;
         declarations(locblksize);
         
         WHILE sym = OSS.procedure DO
            ProcedureDecl;
            IF sym = OSS.semicolon THEN
               OSS.Get(sym)
            ELSE
               OSS.Mark("ProcedureDecl: ; expected")
            END
         END;
         proc.val := OSG.pc;
         OSG.Enter(locblksize);
         
         IF sym = OSS.begin THEN
            OSS.Get(sym);
            StatSequence;
         END;
         IF sym = OSS.end THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("ProcedureDecl: END expected")
         END;
  
         IF sym = OSS.ident THEN
            IF procid # OSS.id THEN
               OSS.Mark("ProcedureDecl: Procedure name expected after END")
            END;
            (* DEBUG *)
            Out.String("PROCEDURE declaration found: ");
            Out.String(procid); Out.Ln;
            OSS.Get(sym)
         END;
         OSG.Return(parblksize - marksize);
         CloseScope;
         OSG.IncLevel(-1)
      END
   END ProcedureDecl;
   
   PROCEDURE Module;
      VAR modid: OSS.Ident; varsize: LONGINT;
   BEGIN
      IF sym = OSS.module THEN
         OSS.Get(sym);
         OSG.Open;
         OpenScope;
         varsize := 0;
         IF sym = OSS.ident THEN
            modid := OSS.id;
            OSS.Get(sym)
         ELSE
            OSS.Mark("Module: identifier expected after MODULE")
         END;
         IF sym = OSS.semicolon THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("Module: ; expected after module name");
         END;
         (* DEBUG *)
         Out.String("MODULE found: "); Out.String(modid); Out.Ln;
         declarations(varsize);
         WHILE sym = OSS.procedure DO
            ProcedureDecl;
            IF sym = OSS.semicolon THEN
               OSS.Get(sym)
            ELSE
               OSS.Mark("Module: ; expected after procedure declarations")
            END
         END;
         OSG.Header(varsize);
         IF sym = OSS.begin THEN
            OSS.Get(sym);
            StatSequence
         END;
         IF sym = OSS.end THEN
            OSS.Get(sym)
         ELSE
            OSS.Mark("Module: END expected")
         END;
         IF sym = OSS.ident THEN
            (*Out.String(OSS.id);*)
            IF modid # OSS.id THEN
               OSS.Mark("Module: module names must match")
            END;
            OSS.Get(sym)
         ELSE
            OSS.Mark("Module: identifier expected after END")
         END;
         IF sym # OSS.period THEN
            OSS.Mark("Module: . expected, got");
            Out.Int(sym, 2)
         END;
         CloseScope;
         IF ~OSS.error THEN
            Out.String("Compile Successful"); Out.Ln;
            OSG.Close;
            OSG.Decode(modid)
         END
      ELSE
         OSS.Mark("Module: MODULE expected")
      END
   END Module;
          
   PROCEDURE Compile(CONST name: ARRAY OF CHAR);
   BEGIN
      OSS.Init(name);
      Out.String("Compiling ");
      Out.String(name); Out.Ln;
      OSS.Get(sym);
      Module
   END Compile;
           
   PROCEDURE enter(cl: INTEGER; n: LONGINT; name: OSS.Ident; type: OSG.Type);
      VAR obj: OSG.Object;
   BEGIN
      NEW(obj);
      obj.class := cl;
      obj.val := n;
      obj.name := name;
      obj.type := type;
      obj.dsc := NIL;
      obj.next := topScope.next;
      topScope.next := obj
   END enter;
   
BEGIN
   Out.String("Oberon-0 compiler");
   Out.Ln;
   NEW(guard);
   guard.class := OSG.Var;
   guard.type := OSG.intType;
   guard.val := 0;
   topScope := NIL;
   OpenScope;
   enter(OSG.Typ, 1, "BOOLEAN", OSG.boolType);
   enter(OSG.Typ, 2, "INTEGER", OSG.intType);
   enter(OSG.Const, 1, "TRUE", OSG.boolType);
   enter(OSG.Const, 2, "FALSE", OSG.boolType);
   enter(OSG.SProc, 1, "Read", NIL);
   enter(OSG.SProc, 2, "Write", NIL);
   enter(OSG.SProc, 3, "WriteHex", NIL);
   enter(OSG.SProc, 4, "WriteLn", NIL);
   universe := topScope;
   Args.GetArg(1, fileName);
   Out.String(fileName);
   IF fileName # "" THEN
      Compile(fileName);
   ELSE
      Out.String("Usage: OSP filename.m"); Out.Ln
   END
END OSP.