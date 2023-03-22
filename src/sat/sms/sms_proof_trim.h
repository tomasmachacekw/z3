class sms_proof_trim {
  m_trail;
  sms_solver s;
 public:
  log_rup(clause* c, unsigned idx);
  log_cp(clause* c, unsigned src, unsigned dst);
  log_del(clause* c, unsigned idx);
  log_asserted(clause* c, unsigned idx);
  void trim();
}
