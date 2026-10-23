AG (FORALL c. (FORALL t. (FORALL z. (FORALL x. (!Write(c, z, t, x) || A ( AX (EF (E ( (!Delete(c, z) && (FORALL y. !Write(c, z, t, y))) W (Read(c, z, t, x) && (EXISTS p. Use(p, x))) ))) U (Delete(c, z) || EXISTS y. Write(c, z, t, y)) ))))))
// S5: Any data stored for a purpose can eventually be processed for it.
//   AG ( FORALL c,t,z,x. write_at(z,x) =>
//          ( AX EF ( !phi_delow W (read_at(z,x) /\ (EX p. use_p(x))) ) ) U phi_delow )
//   where phi_delow = delete_at(z) \/ (EX y. write_at(z,y)),  W is weak until,
//   and   !phi_delow = !delete_at(z) /\ !write_at(z,y).
// Attribute <class c, field t> is universally quantified (the paper's /\_at).
// Trigger is write_at alone: a Create writes every field of the new entry, so
// write_at subsumes create_c(z); keeping the field-free create_c(z) under a
// free t would demand reads of non-existent (class,field) pairs.
//   write_at(z,x)=Write(c,z,t,x)  read_at(z,x)=Read(c,z,t,x)
//   delete_at(z)=Delete(c,z)      use_p(x)=Use(p,x)
// In petshop.spthy these range over  Cbar=Cart, CartItem, Order, OrderItem, CreditCard, Payment, Shipment ; AT=Cart.user, CartItem.quantity, CartItem.cart, CartItem.product, Order.user, OrderItem.quantity, OrderItem.order, OrderItem.product, CreditCard.holderName, CreditCard.expiredMonth, CreditCard.expiredYear, CreditCard.cardNumber_enc, Payment.card, Payment.order, Shipment.address, Shipment.order ; P=Purchasing
