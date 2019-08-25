/* :@

  inductive opt<t> = non | som(t);
  inductive par<s,t> = par(s,t);
  inductive optlst<t> = lst(opt<par<t,optlst<t> > >);

  @*/


