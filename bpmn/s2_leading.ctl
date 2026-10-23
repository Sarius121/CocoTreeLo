FORALL p. (FORALL x. (AG (!Collect(p, x) || (Use(p, x) || (EXISTS z. (EXISTS c. (EXISTS t. (Write(c, z, t, x) && EX (E ( (FORALL y. !Write(c, z, t, y)) U (Read(c, z, t, x) && Use(p, x)) )))))) || (EXISTS a. (Set(a, x) && EX (E ( (FORALL y. !Set(a, y)) U (Get(a, x) && Use(p, x)) ))))))))
// S2: Any data collected for a purpose can eventually be processed for it.
//   FORALL p. FORALL x.
//       AG (collect_p(x) =>
//              use_p(x)                                                  (phi_1)
//           \/ (EX z,c,t. write_at(z,x) /\
//                 EX ( !(EX y. write_at(z,y)) U (read_at(z,x) /\ use_p(x)) ))  (phi_2)
//           \/ (EX a. set_a(x) /\
//                 EX ( !(EX y. set_a(y)) U (get_a(x) /\ use_p(x)) )) )         (phi_3)
// The purpose p, attribute <class c, field t> and argument a are FO variables
// (the paper's /\_p, \/_at and set_a/collect_p families become quantifiers),
// so all event terms use variable arguments only -- no constant extension.
//   collect_p(x)=Collect(p,x)  use_p(x)=Use(p,x)  set_a(y)=Set(a,y)  get_a(x)=Get(a,x)
//   write_at(z,x)=Write(c,z,t,x)  read_at(z,x)=Read(c,z,t,x)
// In petshop.spthy these range over  P=Purchasing ; AT=Cart.user, CartItem.quantity, CartItem.cart, CartItem.product, Order.user, OrderItem.quantity, OrderItem.order, OrderItem.product, CreditCard.holderName, CreditCard.expiredMonth, CreditCard.expiredYear, CreditCard.cardNumber_enc, Payment.card, Payment.order, Shipment.address, Shipment.order ; A=u, c, o, ccn
