#ifndef FIXEDCLASS_H
#define FIXEDCLASS_H

#include <QString>

#include "specialvals.h"

#include "fixedfunction.h"

using namespace std;

class FixedClass
{
private:
  QString name;
  vector<FixedFunction> functions;
public:
  FixedClass(){this->name = "NO_NAME";} // BUG?
  FixedClass(QString name) {this->name = name;}
  QString getName() {return this->name;}
  bool updateFunc(FixedFunction function);
  void addFunction(FixedFunction function) {functions.push_back(function);}
  FixedFunction getFunction(int index) {return functions[index];}
  FixedFunction getFunction(QString name);
  vector<FixedFunction> getFunctions() {return functions;}
};

#endif // FIXEDCLASS_H
