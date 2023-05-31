#ifndef GOTOGO_H
#define GOTOGO_H

#include <QString>
#include <QFile>
#include <QTextStream>

#include <iostream>

#include "fixedclass.h"

using namespace std;

class GoToGo
{
private:
  map<QString, vector<int*>> collect(FixedFunction *func);
public:
  GoToGo();
  void processClasses(map<QString, FixedClass> *classes);
};

#endif // GOTOGO_H
