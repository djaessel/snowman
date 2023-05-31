#ifndef FIXEDFUNCTION_H
#define FIXEDFUNCTION_H

#include <QStringList>

#include "specialvals.h"

class FixedFunction
{
private:
  QString _name;
  QStringList _codeLines;
public:
  FixedFunction() {_name = nullptr;}
  FixedFunction(QString name) : _name(name) {}
  void insertCodeLine(int index, QString line) {_codeLines.insert(index, line);}
  void addCodeLine(QString line) {_codeLines.append(line);}
  void setCodeLines(QStringList codeLines) {_codeLines = codeLines;}
  QStringList getCodeLines() {return _codeLines;}
  QString getName() {return _name;}
};

#endif // FIXEDFUNCTION_H
