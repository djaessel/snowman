#ifndef RAWCLASS_H
#define RAWCLASS_H

#include "specialvals.h"

#include "rawfunction.h"

using namespace std;

class RawClass
{
private:
  QString name;
  vector<RawFunction> functions;
public:
  RawClass(QString name) {this->name = name;}
  QString getName() {return this->name;}
  void addFunction(RawFunction function) {functions.push_back(function);}
  RawFunction getFunction(int index) {return functions[index];}
  vector<RawFunction> getFunctions() {return functions;}
};

#endif // RAWCLASS_H
