#include "fixedclass.h"

FixedFunction FixedClass::getFunction(QString name)
{
  foreach (FixedFunction func, this->functions) {
      if (func.getName() == name) return func;
  }
  return FixedFunction();
}

bool FixedClass::updateFunc(FixedFunction func)
{
  bool success = false;
  int i = 0;
  foreach (FixedFunction funcx, this->functions) {
      if (funcx.getName() == func.getName()){
          this->functions[i] = func;
          success = true;
          break;
      }
      i++;
  }
  return success;
}
