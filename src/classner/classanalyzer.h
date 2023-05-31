#ifndef CLASSANALYZER_H
#define CLASSANALYZER_H

#include <QDir>
#include <QString>
#include <QTextStream>
#include <QThreadPool>

#include <iostream>

#include "fixedclass.h"

class ClassAnalyzer
{
private:
  QString clamsFix(QString allText, QString text);
  void benulf(QString line, map<QString, FixedClass>* classes, map<QString, QString> *class_attributes, QString cls, QString orgCls, QString func, QString fragger = "rdi");
public:
  ClassAnalyzer();
  QStringList findClassAttributesExternal(QString cls, map<QString, FixedClass> *classes);
  QStringList findClassAttributes(QString cls, map<QString, FixedClass> *classes);
  map<QString, QStringList> findClassAttributes(map<QString, FixedClass> *classes);
};

class ClassAnalyzerTask : public QRunnable
{
private:
  uint offset, length;
  ClassAnalyzer* classAnalyzer;
  map<QString, FixedClass> *classes;
  map<QString, QStringList> *classAttributes;

public:
  ClassAnalyzerTask(
      ClassAnalyzer* classAnalyzer,
      map<QString, QStringList>* classAttributes,
      map<QString, FixedClass> *classes,
      uint offset, uint length
      ) {
    this->classAnalyzer = classAnalyzer;
    this->classAttributes = classAttributes;
    this->classes = classes;
    this->offset = offset;
    this->length = length;
  }

  void run() override
  {
      auto it = classes->begin();
      std::advance(it, offset);
      for (uint i = offset; i < length; i++) {
        classAttributes->insert_or_assign(it->first, classAnalyzer->findClassAttributes(it->first, classes));
        classAttributes->insert_or_assign(it->first, classAnalyzer->findClassAttributesExternal(it->first, classes));
        if (i < classes->size() - 1)
            std::advance(it, 1);
      }
  }
};

#endif // CLASSANALYZER_H
