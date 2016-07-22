MODULE Test;
   CONST 
      c1 = 2;
      c2 = 3;
      
   VAR u, v, w: INTEGER;
   
   PROCEDURE p1;
   BEGIN
      u := 1
   END;
   
   PROCEDURE p2;
   BEGIN
      v := 2
   END;
   
BEGIN
   u := 0;
   v := 2*c1 + u;
   w := v DIV c2;
   p1;
   p2
END Test.
