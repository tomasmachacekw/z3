class sms_proof_itp {
  sup;
  itp;
 public:
  log_rup(clause* c, unsigned idx);
  log_cp(clause* c, unsigned src, unsigned dst);
  log_del(clause* c, unsigned idx);
  log_asserted(clause* c, unsigned idx);
  itp();
}
