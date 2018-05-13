///////////////////////////////////////////////////
//
// Author        : Aravind Vijayakumar
// Bugs to       : aravind@ece.ucsb.edu
// Last modified : Mar 9th, 2006
//
// This wraps the CUDD extended precision double library
//
///////////////////////////////////////////////////

struct EpDouble { };
%extend EpDouble {
%pythoncode %{
__doc__ = "This provides the functionality of CUDD's extended precision library. In particular, instances of EpDouble may be passed to DdNode.EpdCountMinterm to retrieve the extended counts. Note also that the basic arithmetic operators (+,-,*,/) have been overloaded for use with EpDouble instances"
%}
  EpDouble() {
    EpDouble * epdouble;
    epdouble = EpdAlloc();
    return epdouble;
  }
  
  EpDouble(double value) {
    EpDouble * epdouble;
    epdouble = EpdAlloc();
    EpdConvert(value,epdouble);
    return epdouble;
  }

  EpDouble(EpDouble *value) {
    EpDouble * epdouble;
    epdouble = EpdAlloc();
    EpdCopy(value,epdouble);
    return epdouble;
  }

  ~EpDouble() {
    EpdFree(self);
  }

  void EpdConvert(double value) { EpdConvert(value,self); }
  void EpdNormalize() { EpdNormalize(self); }
  void EpdNormalizeDecimal() { EpdNormalizeDecimal(self); }
  void EpdMakeInf(int sign) { EpdMakeInf(self, sign); }
  void EpdMakeZero(int sign) { EpdMakeZero(self,sign); }
  void EpdMakeNan() { EpdMakeNan(self); };
  void EpdCopy(EpDouble *to) { EpdCopy(self,to); }

  %apply double *OUTPUT { double *dum_value };
  %apply int *OUTPUT { int *dum_exponent };
  void EpdGetValueAndDecimalExponent(double *dum_value, int *dum_exponent) { return EpdGetValueAndDecimalExponent(self,dum_value,dum_exponent); }
  //void EpdGetString(EpDouble *epd, char *str);

  // Arithmetic operations
  void EpdMultiply(double value) { EpdMultiply(self,value); }
  void EpdMultiply2(EpDouble *epd2) { EpdMultiply2(self,epd2); }
  void EpdMultiply2Decimal(EpDouble *epd2) { EpdMultiply2Decimal(self,epd2); }
  void EpdMultiply3(EpDouble *epd2, EpDouble *epd3) { EpdMultiply3(self,epd2,epd3); }
  void EpdMultiply3Decimal(EpDouble *epd2, EpDouble *epd3) { EpdMultiply3Decimal(self,epd2,epd3); }
  void EpdDivide(double value) { EpdDivide(self,value); }
  void EpdDivide2(EpDouble *epd2) { EpdDivide2(self,epd2); }
  void EpdDivide3(EpDouble *epd2, EpDouble *epd3) { EpdDivide3(self,epd2,epd3); }
  void EpdAdd(double value) { EpdAdd(self,value); }
  void EpdAdd2(EpDouble *epd2) { EpdAdd2(self,epd2); }
  void EpdAdd3(EpDouble *epd2, EpDouble *epd3) { EpdAdd3(self,epd2,epd3); }
  void EpdSubtract(double value) { EpdSubtract(self,value); }
  void EpdSubtract2(EpDouble *epd2) { EpdSubtract2(self,epd2); }
  void EpdSubtract3(EpDouble *epd2, EpDouble *epd3) { EpdSubtract3(self,epd2,epd3); }
  void EpdPow2(int n) { EpdPow2(n,self); }
  void EpdPow2Decimal(int n) { EpdPow2Decimal(n,self); }
  ///// For Python operators
  %newobject __add__; EpDouble * __add__ (EpDouble *other) { EpDouble *result = EpdAlloc(); EpdAdd3(self,other,result); return result; }
  %newobject __add__; EpDouble * __add__ (double other) { EpDouble *result = EpdAlloc(); EpdCopy(self,result); EpdAdd(result,other); return result; }
  %newobject __sub__; EpDouble * __sub__ (EpDouble *other) { EpDouble *result = EpdAlloc(); EpdSubtract3(self,other,result); return result; }
  %newobject __sub__; EpDouble * __sub__ (double other) { EpDouble *result = EpdAlloc(); EpdCopy(self,result); EpdSubtract(result,other); return result; }
  %newobject __mul__; EpDouble * __mul__ (EpDouble *other) { EpDouble *result = EpdAlloc(); EpdMultiply3(self,other,result); return result; }
  %newobject __mul__; EpDouble * __mul__ (double other) { EpDouble *result = EpdAlloc(); EpdCopy(self,result); EpdMultiply(result,other); return result; }
  %newobject __div__; EpDouble * __div__ (EpDouble *other) { EpDouble *result = EpdAlloc(); EpdDivide3(self,other,result); return result; }
  %newobject __div__; EpDouble * __div__ (double other) { EpDouble *result = EpdAlloc(); EpdDivide(self,other); return result; }
  
  // Logical queries
  bool EpdCmp(EpDouble *other) { return EpdCmp((const char *) self, (const char *) other) ? true : false; }
  bool EpdIsInf() { return EpdIsInf(self) ? true : false; }
  bool EpdIsZero() { return EpdIsZero(self) ? true : false; }
  bool EpdIsNan() { return EpdIsNan(self) ? true : false; }
  bool EpdIsNanOrInf() { return EpdIsNanOrInf(self) ? true : false; }
  ///// For Python operators
  bool __nonzero__() { return EpdIsZero(self) ? false : true; }
  bool __eq__(EpDouble *other) { return EpdCmp((const char *) self, (const char *) other) ? false : true; }
  bool __ne__(EpDouble *other) { return EpdCmp((const char *) self, (const char *) other) ? true : false; }

};

// Some general non-epd specific functions in the package
int EpdGetExponent(double value);
int EpdGetExponentDecimal(double value);
bool IsInfDouble(double value) { return IsInfDouble(value) ? true : false; }
bool IsNanDouble(double value) { return IsNanDouble(value) ? true : false; }
bool IsNanOrInfDouble(double value) { return IsNanOrInfDouble(value) ? true : false; }
